import Verity.Core.Free.TypedIR
import Compiler.CompilationModel

namespace Verity.Core.Free
open Compiler.CompilationModel

/-- Existential wrapper for typed IR expressions returned by compilation. -/
structure SomeTExpr where
  ty : Ty
  expr : TExpr ty

/-- Compiler state threaded through `CompileM`. -/
structure CompileState where
  nextId : Nat := 0
  vars : List (String × TVar) := []
  params : Array TVar := #[]
  locals : Array TVar := #[]
  body : Array TStmt := #[]

abbrev CompileM := StateT CompileState (Except String)

private def lookupVar (name : String) : CompileM TVar := do
  match (← get).vars.find? (fun (entry : String × TVar) => entry.1 == name) with
  | some (_, v) =>
      return v
  | none =>
      throw s!"Typed IR compile error: unknown variable '{name}'"

private def bindVar (name : String) (v : TVar) : CompileM Unit :=
  modify fun st => { st with vars := (name, v) :: st.vars }

/-- Allocate a fresh typed SSA variable. -/
def freshVar (ty : Ty) : CompileM { v : TVar // v.ty = ty } := do
  let st ← get
  let v : TVar := { id := st.nextId, ty := ty }
  set { st with nextId := st.nextId + 1 }
  return ⟨v, rfl⟩

private def pushParam (v : TVar) : CompileM Unit :=
  modify fun st => { st with params := st.params.push v }

private def pushLocal (v : TVar) : CompileM Unit :=
  modify fun st => { st with locals := st.locals.push v }

private def emit (stmt : TStmt) : CompileM Unit :=
  modify fun st => { st with body := st.body.push stmt }

private def paramTypeToTy : ParamType → Except String Ty
  | .uint256 => Except.ok Ty.uint256
  | .uint8 => Except.ok Ty.uint256
  | .address => Except.ok Ty.address
  | .bool => Except.ok Ty.bool
  | .bytes32 => Except.ok Ty.uint256
  | .tuple _ => Except.error "Typed IR compile error: tuple params are not yet supported"
  | .array _ => Except.error "Typed IR compile error: dynamic array params are not yet supported"
  | .fixedArray _ _ => Except.error "Typed IR compile error: fixed array params are not yet supported"
  | .bytes => Except.error "Typed IR compile error: bytes params are not yet supported"

private def fieldTypeToTy : FieldType → Except String Ty
  | .uint256 => Except.ok Ty.uint256
  | .address => Except.ok Ty.address
  | .mappingTyped _ => Except.ok Ty.uint256
  | .mappingStruct _ _ => Except.ok Ty.uint256
  | .mappingStruct2 _ _ _ => Except.ok Ty.uint256

private def asUInt256 (e : SomeTExpr) : Except String (TExpr Ty.uint256) :=
  match e with
  | ⟨Ty.uint256, expr⟩ => Except.ok expr
  -- EVM treats booleans as 0/1 words; coerce via ite to preserve typed-IR invariants.
  | ⟨Ty.bool, expr⟩ => Except.ok (TExpr.ite expr (TExpr.uintLit 1) (TExpr.uintLit 0))
  | ⟨ty, _⟩ => Except.error s!"Typed IR compile error: expected uint256 expression, got {repr ty}"

private def asAddress (e : SomeTExpr) : Except String (TExpr Ty.address) :=
  match e with
  | ⟨Ty.address, expr⟩ => Except.ok expr
  | ⟨ty, _⟩ => Except.error s!"Typed IR compile error: expected address expression, got {repr ty}"

private def asBool (e : SomeTExpr) : Except String (TExpr Ty.bool) :=
  match e with
  | ⟨Ty.bool, expr⟩ => Except.ok expr
  | ⟨ty, _⟩ => Except.error s!"Typed IR compile error: expected bool expression, got {repr ty}"

private def compileStorageRead (fields : List Field) (fieldName : String) : Except String SomeTExpr := do
  match findFieldWithResolvedSlot fields fieldName with
  | none =>
      throw s!"Typed IR compile error: unknown storage field '{fieldName}'"
  | some (field, slot) =>
      match (← fieldTypeToTy field.ty) with
      | Ty.uint256 =>
          return ⟨Ty.uint256, TExpr.getStorage slot⟩
      | Ty.address =>
          return ⟨Ty.address, TExpr.getStorageAddr slot⟩
      | Ty.bool =>
          throw s!"Typed IR compile error: storage bool field '{fieldName}' unsupported in phase 2.1"
      | Ty.unit =>
          throw s!"Typed IR compile error: storage unit field '{fieldName}' unsupported"

mutual

private def compileExpr (fields : List Field) : Expr → CompileM SomeTExpr
  | .literal n =>
      return ⟨Ty.uint256, TExpr.uintLit n⟩
  | .param name => do
      let v ← lookupVar name
      return ⟨v.ty, TExpr.var v⟩
  | .localVar name => do
      let v ← lookupVar name
      return ⟨v.ty, TExpr.var v⟩
  | .storage fieldName =>
      liftExcept <| compileStorageRead fields fieldName
  | .mapping field key => do
      let keyExpr ← compileExpr fields key
      let keyAddr ← liftExcept <| asAddress keyExpr
      match findFieldSlot fields field with
      | some slot =>
          return ⟨Ty.uint256, TExpr.getMapping slot keyAddr⟩
      | none =>
          throw s!"Typed IR compile error: unknown mapping field '{field}'"
  | .mappingUint field key => do
      let keyExpr ← compileExpr fields key
      let keyUint ← liftExcept <| asUInt256 keyExpr
      match findFieldSlot fields field with
      | some slot =>
          return ⟨Ty.uint256, TExpr.getMappingUint slot keyUint⟩
      | none =>
          throw s!"Typed IR compile error: unknown mapping field '{field}'"
  | .mapping2 field key1 key2 => do
      let key1Expr ← liftExcept <| asAddress (← compileExpr fields key1)
      let key2Expr ← liftExcept <| asAddress (← compileExpr fields key2)
      match findFieldSlot fields field with
      | some slot =>
          return ⟨Ty.uint256, TExpr.getMapping2 slot key1Expr key2Expr⟩
      | none =>
          throw s!"Typed IR compile error: unknown mapping field '{field}'"
  | .caller => return ⟨Ty.address, TExpr.sender⟩
  | .contractAddress => return ⟨Ty.address, TExpr.this⟩
  | .msgValue => return ⟨Ty.uint256, TExpr.msgValue⟩
  | .blockTimestamp => return ⟨Ty.uint256, TExpr.blockTimestamp⟩
  | .add a b => do
      let a' ← liftExcept <| asUInt256 (← compileExpr fields a)
      let b' ← liftExcept <| asUInt256 (← compileExpr fields b)
      return ⟨Ty.uint256, TExpr.add a' b'⟩
  | .sub a b => do
      let a' ← liftExcept <| asUInt256 (← compileExpr fields a)
      let b' ← liftExcept <| asUInt256 (← compileExpr fields b)
      return ⟨Ty.uint256, TExpr.sub a' b'⟩
  | .mul a b => do
      let a' ← liftExcept <| asUInt256 (← compileExpr fields a)
      let b' ← liftExcept <| asUInt256 (← compileExpr fields b)
      return ⟨Ty.uint256, TExpr.mul a' b'⟩
  | .lt a b => do
      let a' ← liftExcept <| asUInt256 (← compileExpr fields a)
      let b' ← liftExcept <| asUInt256 (← compileExpr fields b)
      return ⟨Ty.bool, TExpr.lt a' b'⟩
  | .ge a b => do
      let a' ← liftExcept <| asUInt256 (← compileExpr fields a)
      let b' ← liftExcept <| asUInt256 (← compileExpr fields b)
      return ⟨Ty.bool, TExpr.not (TExpr.lt a' b')⟩
  | .gt a b => do
      let a' ← liftExcept <| asUInt256 (← compileExpr fields a)
      let b' ← liftExcept <| asUInt256 (← compileExpr fields b)
      return ⟨Ty.bool, TExpr.lt b' a'⟩
  | .le a b => do
      let a' ← liftExcept <| asUInt256 (← compileExpr fields a)
      let b' ← liftExcept <| asUInt256 (← compileExpr fields b)
      return ⟨Ty.bool, TExpr.not (TExpr.lt b' a')⟩
  | .eq a b => do
      let a' ← compileExpr fields a
      let b' ← compileExpr fields b
      match a', b' with
      | ⟨Ty.uint256, aExpr⟩, ⟨Ty.uint256, bExpr⟩ => return ⟨Ty.bool, TExpr.eq aExpr bExpr⟩
      | ⟨Ty.address, aExpr⟩, ⟨Ty.address, bExpr⟩ => return ⟨Ty.bool, TExpr.eq aExpr bExpr⟩
      | ⟨Ty.bool, aExpr⟩, ⟨Ty.bool, bExpr⟩ => return ⟨Ty.bool, TExpr.eq aExpr bExpr⟩
      | ⟨Ty.unit, aExpr⟩, ⟨Ty.unit, bExpr⟩ => return ⟨Ty.bool, TExpr.eq aExpr bExpr⟩
      | ⟨aTy, _⟩, ⟨bTy, _⟩ =>
          throw s!"Typed IR compile error: eq operand type mismatch ({repr aTy} vs {repr bTy})"
  | .logicalAnd a b => do
      let a' ← liftExcept <| asBool (← compileExpr fields a)
      let b' ← liftExcept <| asBool (← compileExpr fields b)
      return ⟨Ty.bool, TExpr.and a' b'⟩
  | .logicalOr a b => do
      let a' ← liftExcept <| asBool (← compileExpr fields a)
      let b' ← liftExcept <| asBool (← compileExpr fields b)
      return ⟨Ty.bool, TExpr.or a' b'⟩
  | .logicalNot a => do
      let a' ← liftExcept <| asBool (← compileExpr fields a)
      return ⟨Ty.bool, TExpr.not a'⟩
  | .ite cond thenVal elseVal => do
      let c ← liftExcept <| asBool (← compileExpr fields cond)
      let t ← compileExpr fields thenVal
      let e ← compileExpr fields elseVal
      match t, e with
      | ⟨Ty.uint256, tExpr⟩, ⟨Ty.uint256, eExpr⟩ => return ⟨Ty.uint256, TExpr.ite c tExpr eExpr⟩
      | ⟨Ty.address, tExpr⟩, ⟨Ty.address, eExpr⟩ => return ⟨Ty.address, TExpr.ite c tExpr eExpr⟩
      | ⟨Ty.bool, tExpr⟩, ⟨Ty.bool, eExpr⟩ => return ⟨Ty.bool, TExpr.ite c tExpr eExpr⟩
      | ⟨Ty.unit, tExpr⟩, ⟨Ty.unit, eExpr⟩ => return ⟨Ty.unit, TExpr.ite c tExpr eExpr⟩
      | ⟨tTy, _⟩, ⟨eTy, _⟩ =>
          throw s!"Typed IR compile error: ite branch type mismatch ({repr tTy} vs {repr eTy})"
  | expr =>
      throw s!"Typed IR compile error: unsupported expression form in phase 2.1: {repr expr}"

private def emitSSABind (name : String) (rhs : SomeTExpr) : CompileM Unit :=
  match rhs with
  | ⟨ty, expr⟩ => do
      let ⟨dst, hty⟩ ← freshVar ty
      let rhs' : TExpr dst.ty := by
        simpa [hty] using expr
      bindVar name dst
      pushLocal dst
      emit (.let_ dst rhs')

private def compileStmt (fields : List Field) : Stmt → CompileM Unit
  | .letVar name value => do
      emitSSABind name (← compileExpr fields value)
  | .assignVar name value => do
      let old ← lookupVar name
      let rhs ← compileExpr fields value
      if rhs.ty != old.ty then
        throw s!"Typed IR compile error: assignment type mismatch for '{name}'"
      emitSSABind name rhs
  | .setStorage fieldName value => do
      let rhs ← compileExpr fields value
      match findFieldWithResolvedSlot fields fieldName with
      | none =>
          throw s!"Typed IR compile error: unknown storage field '{fieldName}'"
      | some (field, slot) =>
          match (← fieldTypeToTy field.ty), rhs with
          | Ty.uint256, ⟨Ty.uint256, expr⟩ => emit (.setStorage slot expr)
          | Ty.address, ⟨Ty.address, expr⟩ => emit (.setStorageAddr slot expr)
          | expectedTy, ⟨actualTy, _⟩ =>
              throw s!"Typed IR compile error: setStorage type mismatch for '{fieldName}' (expected {repr expectedTy}, got {repr actualTy})"
  | .setMapping fieldName key value => do
      let keyExpr ← liftExcept <| asAddress (← compileExpr fields key)
      let valueExpr ← liftExcept <| asUInt256 (← compileExpr fields value)
      match findFieldSlot fields fieldName with
      | some slot => emit (.setMapping slot keyExpr valueExpr)
      | none => throw s!"Typed IR compile error: unknown mapping field '{fieldName}'"
  | .setMappingUint fieldName key value => do
      let keyExpr ← liftExcept <| asUInt256 (← compileExpr fields key)
      let valueExpr ← liftExcept <| asUInt256 (← compileExpr fields value)
      match findFieldSlot fields fieldName with
      | some slot => emit (.setMappingUint slot keyExpr valueExpr)
      | none => throw s!"Typed IR compile error: unknown mapping field '{fieldName}'"
  | .setMapping2 fieldName key1 key2 value => do
      let key1Expr ← liftExcept <| asAddress (← compileExpr fields key1)
      let key2Expr ← liftExcept <| asAddress (← compileExpr fields key2)
      let valueExpr ← liftExcept <| asUInt256 (← compileExpr fields value)
      match findFieldSlot fields fieldName with
      | some slot => emit (.setMapping2 slot key1Expr key2Expr valueExpr)
      | none => throw s!"Typed IR compile error: unknown mapping field '{fieldName}'"
  | .require cond message => do
      let condExpr ← liftExcept <| asBool (← compileExpr fields cond)
      emit (.if_ condExpr [] [.revert message])
  | .ite cond thenBranch elseBranch => do
      let condExpr ← liftExcept <| asBool (← compileExpr fields cond)
      let thenStmts ← compileBranch fields thenBranch
      let elseStmts ← compileBranch fields elseBranch
      emit (.if_ condExpr thenStmts elseStmts)
  | .stop =>
      emit .stop
  | .return value => do
      let rhs ← compileExpr fields value
      match rhs with
      | ⟨Ty.uint256, expr⟩ => emit (.returnUint expr)
      | ⟨Ty.address, expr⟩ => emit (.returnAddr expr)
      | ⟨Ty.bool, expr⟩ => emit (.returnUint (TExpr.ite expr (TExpr.uintLit 1) (TExpr.uintLit 0)))
      | ⟨ty, _⟩ => throw s!"Typed IR compile error: unsupported return type {repr ty}"
  | .returnValues values =>
      match values with
      | [] =>
          emit .stop
      | [value] => do
          let rhs ← compileExpr fields value
          match rhs with
          | ⟨Ty.uint256, expr⟩ => emit (.returnUint expr)
          | ⟨Ty.address, expr⟩ => emit (.returnAddr expr)
          | ⟨Ty.bool, expr⟩ => emit (.returnUint (TExpr.ite expr (TExpr.uintLit 1) (TExpr.uintLit 0)))
          | ⟨ty, _⟩ => throw s!"Typed IR compile error: unsupported return type {repr ty}"
      | _ =>
          throw "Typed IR compile error: multiple return values are not supported in phase 2.4"
  | stmt =>
      throw s!"Typed IR compile error: unsupported statement form in phase 2.1: {repr stmt}"

/-- Compile a statement list in source order.
This structural recursion is the induction surface for generic correctness lemmas. -/
def compileStmts (fields : List Field) : List Stmt → CompileM Unit
  | [] => return ()
  | stmt :: rest => do
      compileStmt fields stmt
      compileStmts fields rest

private def compileBranch (fields : List Field) (stmts : List Stmt) : CompileM (List TStmt) := do
  let startState ← get
  set { startState with body := #[] }
  compileStmts fields stmts
  let branchState ← get
  -- Restore parent state but preserve branch-created locals so that
  -- TBlock.locals remains a complete list of all variables in the body.
  set { startState with nextId := branchState.nextId
                        locals := branchState.locals }
  return branchState.body.toList

end

private def registerParam (param : Param) : CompileM Unit := do
  let ty ← liftExcept <| paramTypeToTy param.ty
  let ⟨v, _⟩ ← freshVar ty
  bindVar param.name v
  pushParam v

/-- Compile a single `CompilationModel` function into typed IR. -/
def compileFunctionToTBlock (spec : CompilationModel) (fn : FunctionSpec) : Except String TBlock := do
  let (_, st) ← ((do
      for p in fn.params do
        registerParam p
      compileStmts spec.fields fn.body
      return ()) : CompileM Unit).run {}
  return { params := st.params.toList
           locals := st.locals.toList
           body := st.body.toList }

/-- Compile a named function from a `CompilationModel` to typed IR. -/
def compileFunctionNamed (spec : CompilationModel) (functionName : String) : Except String TBlock := do
  match spec.functions.find? (fun fn => fn.name == functionName) with
  | some fn => compileFunctionToTBlock spec fn
  | none => throw s!"Typed IR compile error: function '{functionName}' not found in spec '{spec.name}'"

/-- Single-statement compilation shape for the supported subset:
`setStorage fieldName (literal n)` lowers to one typed `setStorage` when the
field resolves to a uint256 slot. -/
theorem compileStmts_single_setStorage_literal_run
    (fields : List Field) (fieldName : String) (slot : Nat)
    (n : Nat) (st : CompileState)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    (compileStmts fields [Stmt.setStorage fieldName (Expr.literal n)]).run st =
      Except.ok ((), { st with body := st.body.push (TStmt.setStorage slot (TExpr.uintLit n)) }) := by
  simp [compileStmts, compileStmt, compileExpr, fieldTypeToTy, hfind, emit]
  rfl

/-- Two-statement compilation shape for a broader supported subset:
`letVar tmp (literal n); setStorage fieldName (localVar tmp)` lowers to one SSA `let_`
followed by one typed `setStorage`, from an empty compile state. -/
theorem compileStmts_let_literal_setStorage_local_run
    (fields : List Field) (fieldName tmp : String) (slot : Nat)
    (n : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    (compileStmts fields
      [Stmt.letVar tmp (Expr.literal n), Stmt.setStorage fieldName (Expr.localVar tmp)]).run {} =
      Except.ok ((),
        { nextId := 1
          vars := [(tmp, { id := 0, ty := Ty.uint256 })]
          params := #[]
          locals := #[{ id := 0, ty := Ty.uint256 }]
          body := #[
            TStmt.let_ { id := 0, ty := Ty.uint256 } (TExpr.uintLit n),
            TStmt.setStorage slot (TExpr.var { id := 0, ty := Ty.uint256 })
          ] }) := by
  simp [compileStmts, compileStmt, compileExpr, emitSSABind, freshVar, bindVar, pushLocal,
    lookupVar, fieldTypeToTy, hfind, emit]
  rfl

/-- Three-statement compilation shape for a broader supported subset:
`letVar tmp (literal n); assignVar tmp (literal m); setStorage fieldName (localVar tmp)`
lowers to two SSA `let_` bindings and one typed `setStorage`, from an empty compile state. -/
theorem compileStmts_let_assign_literal_setStorage_local_run
    (fields : List Field) (fieldName tmp : String) (slot : Nat)
    (n m : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    (compileStmts fields
      [ Stmt.letVar tmp (Expr.literal n)
      , Stmt.assignVar tmp (Expr.literal m)
      , Stmt.setStorage fieldName (Expr.localVar tmp)
      ]).run {} =
      Except.ok ((),
        { nextId := 2
          vars := [ (tmp, { id := 1, ty := Ty.uint256 })
                  , (tmp, { id := 0, ty := Ty.uint256 })]
          params := #[]
          locals := #[{ id := 0, ty := Ty.uint256 }, { id := 1, ty := Ty.uint256 }]
          body := #[
            TStmt.let_ { id := 0, ty := Ty.uint256 } (TExpr.uintLit n),
            TStmt.let_ { id := 1, ty := Ty.uint256 } (TExpr.uintLit m),
            TStmt.setStorage slot (TExpr.var { id := 1, ty := Ty.uint256 })
          ] }) := by
  simp [compileStmts, compileStmt, compileExpr, emitSSABind, freshVar, bindVar, pushLocal,
    lookupVar, fieldTypeToTy, hfind, emit]
  rfl

/-- Three-statement compilation shape for an arithmetic supported subset:
`letVar tmp (literal n); assignVar tmp (add (localVar tmp) (literal m)); setStorage fieldName (localVar tmp)`
lowers to two SSA `let_` bindings and one typed `setStorage`, from an empty compile state. -/
theorem compileStmts_let_assign_add_literal_setStorage_local_run
    (fields : List Field) (fieldName tmp : String) (slot : Nat)
    (n m : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    (compileStmts fields
      [ Stmt.letVar tmp (Expr.literal n)
      , Stmt.assignVar tmp (Expr.add (Expr.localVar tmp) (Expr.literal m))
      , Stmt.setStorage fieldName (Expr.localVar tmp)
      ]).run {} =
      Except.ok ((),
        { nextId := 2
          vars := [ (tmp, { id := 1, ty := Ty.uint256 })
                  , (tmp, { id := 0, ty := Ty.uint256 })]
          params := #[]
          locals := #[{ id := 0, ty := Ty.uint256 }, { id := 1, ty := Ty.uint256 }]
          body := #[
            TStmt.let_ { id := 0, ty := Ty.uint256 } (TExpr.uintLit n),
            TStmt.let_ { id := 1, ty := Ty.uint256 }
              (TExpr.add (TExpr.var { id := 0, ty := Ty.uint256 }) (TExpr.uintLit m)),
            TStmt.setStorage slot (TExpr.var { id := 1, ty := Ty.uint256 })
          ] }) := by
  simp [compileStmts, compileStmt, compileExpr, emitSSABind, freshVar, bindVar, pushLocal,
    lookupVar, fieldTypeToTy, hfind, emit]
  rfl

/-- Three-statement compilation shape for an arithmetic supported subset:
`letVar tmp (literal n); assignVar tmp (sub (localVar tmp) (literal m)); setStorage fieldName (localVar tmp)`
lowers to two SSA `let_` bindings and one typed `setStorage`, from an empty compile state. -/
theorem compileStmts_let_assign_sub_literal_setStorage_local_run
    (fields : List Field) (fieldName tmp : String) (slot : Nat)
    (n m : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    (compileStmts fields
      [ Stmt.letVar tmp (Expr.literal n)
      , Stmt.assignVar tmp (Expr.sub (Expr.localVar tmp) (Expr.literal m))
      , Stmt.setStorage fieldName (Expr.localVar tmp)
      ]).run {} =
      Except.ok ((),
        { nextId := 2
          vars := [ (tmp, { id := 1, ty := Ty.uint256 })
                  , (tmp, { id := 0, ty := Ty.uint256 })]
          params := #[]
          locals := #[{ id := 0, ty := Ty.uint256 }, { id := 1, ty := Ty.uint256 }]
          body := #[
            TStmt.let_ { id := 0, ty := Ty.uint256 } (TExpr.uintLit n),
            TStmt.let_ { id := 1, ty := Ty.uint256 }
              (TExpr.sub (TExpr.var { id := 0, ty := Ty.uint256 }) (TExpr.uintLit m)),
            TStmt.setStorage slot (TExpr.var { id := 1, ty := Ty.uint256 })
          ] }) := by
  simp [compileStmts, compileStmt, compileExpr, emitSSABind, freshVar, bindVar, pushLocal,
    lookupVar, fieldTypeToTy, hfind, emit]
  rfl

/-- Three-statement compilation shape for an arithmetic supported subset:
`letVar tmp (literal n); assignVar tmp (mul (localVar tmp) (literal m)); setStorage fieldName (localVar tmp)`
lowers to two SSA `let_` bindings and one typed `setStorage`, from an empty compile state. -/
theorem compileStmts_let_assign_mul_literal_setStorage_local_run
    (fields : List Field) (fieldName tmp : String) (slot : Nat)
    (n m : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    (compileStmts fields
      [ Stmt.letVar tmp (Expr.literal n)
      , Stmt.assignVar tmp (Expr.mul (Expr.localVar tmp) (Expr.literal m))
      , Stmt.setStorage fieldName (Expr.localVar tmp)
      ]).run {} =
      Except.ok ((),
        { nextId := 2
          vars := [ (tmp, { id := 1, ty := Ty.uint256 })
                  , (tmp, { id := 0, ty := Ty.uint256 })]
          params := #[]
          locals := #[{ id := 0, ty := Ty.uint256 }, { id := 1, ty := Ty.uint256 }]
          body := #[
            TStmt.let_ { id := 0, ty := Ty.uint256 } (TExpr.uintLit n),
            TStmt.let_ { id := 1, ty := Ty.uint256 }
              (TExpr.mul (TExpr.var { id := 0, ty := Ty.uint256 }) (TExpr.uintLit m)),
            TStmt.setStorage slot (TExpr.var { id := 1, ty := Ty.uint256 })
          ] }) := by
  simp [compileStmts, compileStmt, compileExpr, emitSSABind, freshVar, bindVar, pushLocal,
    lookupVar, fieldTypeToTy, hfind, emit]
  rfl

/-- Single-statement compilation shape for a broader supported subset:
`return (literal n)` lowers to one typed `returnUint`, from any initial compile state. -/
theorem compileStmts_single_return_literal_run
    (fields : List Field) (n : Nat) (st : CompileState) :
    (compileStmts fields [Stmt.return (Expr.literal n)]).run st =
      Except.ok ((), { st with body := st.body.push (TStmt.returnUint (TExpr.uintLit n)) }) := by
  simp [compileStmts, compileStmt, compileExpr, emit]
  rfl

/-- Two-statement compilation shape for a broader supported subset:
`letVar tmp (literal n); return (localVar tmp)` lowers to one SSA `let_`
followed by one typed `returnUint`, from an empty compile state. -/
theorem compileStmts_let_return_local_literal_run
    (fields : List Field) (tmp : String) (n : Nat) :
    (compileStmts fields
      [Stmt.letVar tmp (Expr.literal n), Stmt.return (Expr.localVar tmp)]).run {} =
      Except.ok ((),
        { nextId := 1
          vars := [(tmp, { id := 0, ty := Ty.uint256 })]
          params := #[]
          locals := #[{ id := 0, ty := Ty.uint256 }]
          body := #[
            TStmt.let_ { id := 0, ty := Ty.uint256 } (TExpr.uintLit n),
            TStmt.returnUint (TExpr.var { id := 0, ty := Ty.uint256 })
          ] }) := by
  simp [compileStmts, compileStmt, compileExpr, emitSSABind, freshVar, bindVar, pushLocal,
    lookupVar, emit]
  rfl

/-- Single-statement compilation shape for a broader supported branch subset:
`ite (eq (literal n) (literal m))
     [setStorage fieldName (literal thenVal)]
     [setStorage fieldName (literal elseVal)]`
lowers to one typed `if_` with two typed `setStorage` branches, from an empty compile state. -/
theorem compileStmts_single_ite_eq_setStorage_literals_run
    (fields : List Field) (fieldName : String) (slot : Nat)
    (n m thenVal elseVal : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    (compileStmts fields
      [Stmt.ite
        (Expr.eq (Expr.literal n) (Expr.literal m))
        [Stmt.setStorage fieldName (Expr.literal thenVal)]
        [Stmt.setStorage fieldName (Expr.literal elseVal)] ]).run {} =
      Except.ok ((),
        { nextId := 0
          vars := []
          params := #[]
          locals := #[]
          body := #[
            TStmt.if_
              (TExpr.eq (TExpr.uintLit n) (TExpr.uintLit m))
              [TStmt.setStorage slot (TExpr.uintLit thenVal)]
              [TStmt.setStorage slot (TExpr.uintLit elseVal)]
          ] }) := by
  simp [compileStmts, compileStmt, compileExpr, compileBranch, fieldTypeToTy, hfind, emit]
  rfl

/-- Single-statement compilation shape for a broader supported require subset:
`require (eq (literal n) (literal m)) message`
lowers to one typed `if_` with an else-branch `revert`, from an empty compile state. -/
theorem compileStmts_single_require_eq_literals_run
    (fields : List Field) (message : String) (n m : Nat) :
    (compileStmts fields
      [Stmt.require (Expr.eq (Expr.literal n) (Expr.literal m)) message]).run {} =
      Except.ok ((),
        { nextId := 0
          vars := []
          params := #[]
          locals := #[]
          body := #[
            TStmt.if_
              (TExpr.eq (TExpr.uintLit n) (TExpr.uintLit m))
              []
              [TStmt.revert message]
          ] }) := by
  simp [compileStmts, compileStmt, compileExpr, emit]
  rfl

/-- Single-statement compilation shape for a broader supported require subset:
`require (lt (literal n) (literal m)) message`
lowers to one typed `if_` with an else-branch `revert`, from an empty compile state. -/
theorem compileStmts_single_require_lt_literals_run
    (fields : List Field) (message : String) (n m : Nat) :
    (compileStmts fields
      [Stmt.require (Expr.lt (Expr.literal n) (Expr.literal m)) message]).run {} =
      Except.ok ((),
        { nextId := 0
          vars := []
          params := #[]
          locals := #[]
          body := #[
            TStmt.if_
              (TExpr.lt (TExpr.uintLit n) (TExpr.uintLit m))
              []
              [TStmt.revert message]
          ] }) := by
  simp [compileStmts, compileStmt, compileExpr, emit]
  rfl

end Verity.Core.Free
