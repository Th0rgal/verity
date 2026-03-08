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
  -- Complex ABI params enter the compilation model as calldata head words/offsets.
  -- The typed IR can track those heads as ordinary uint256 values.
  | .string => Except.ok Ty.uint256
  | .tuple _ => Except.ok Ty.uint256
  | .array _ => Except.ok Ty.uint256
  | .fixedArray _ _ => Except.ok Ty.uint256
  | .bytes => Except.ok Ty.uint256

private def fieldTypeToTy : FieldType → Except String Ty
  | .uint256 => Except.ok Ty.uint256
  | .address => Except.ok Ty.address
  | .mappingTyped _ => Except.ok Ty.uint256
  | .mappingStruct _ _ => Except.ok Ty.uint256
  | .mappingStruct2 _ _ _ => Except.ok Ty.uint256

private def asUInt256 (e : SomeTExpr) : Except String (TExpr Ty.uint256) :=
  match e with
  | ⟨Ty.uint256, expr⟩ => Except.ok expr
  | ⟨Ty.address, expr⟩ => Except.ok (TExpr.addrToUint expr)
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

private def ensureTypedIRAddressFieldSupported (fieldName : String) (field : Field) :
    Except String Unit := do
  match field.packedBits with
  | some _ =>
      throw s!"Typed IR compile error: storage field '{fieldName}' uses packedBits; address-typed packed storage is not yet supported in typed IR"
  | none => Except.ok ()

@[simp] private theorem ensureTypedIRAddressFieldSupported_none
    (fieldName name : String) (ty : FieldType) (slot : Option Nat) (aliasSlots : List Nat) :
    ensureTypedIRAddressFieldSupported fieldName
      { name := name, ty := ty, slot := slot, packedBits := none, aliasSlots := aliasSlots } =
        Except.ok () := rfl

private def compileStorageRead (fields : List Field) (fieldName : String)
    (requireAddressField : Bool := false) : Except String SomeTExpr := do
  match findFieldWithResolvedSlot fields fieldName with
  | none =>
      throw s!"Typed IR compile error: unknown storage field '{fieldName}'"
  | some (field, slot) =>
      if requireAddressField then
        match field.ty with
        | .address => ensureTypedIRAddressFieldSupported fieldName field
        | _ =>
            throw s!"Typed IR compile error: storage field '{fieldName}' is not address-typed; use Expr.storage instead"
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
  | .storageAddr fieldName =>
      liftExcept <| compileStorageRead fields fieldName true
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
  | .chainid => return ⟨Ty.uint256, TExpr.chainid⟩
  | .msgValue => return ⟨Ty.uint256, TExpr.msgValue⟩
  | .blockTimestamp => return ⟨Ty.uint256, TExpr.blockTimestamp⟩
  | .blockNumber => return ⟨Ty.uint256, TExpr.blockNumber⟩
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
  | .div a b => do
      let a' ← liftExcept <| asUInt256 (← compileExpr fields a)
      let b' ← liftExcept <| asUInt256 (← compileExpr fields b)
      return ⟨Ty.uint256, TExpr.div a' b'⟩
  | .mod a b => do
      let a' ← liftExcept <| asUInt256 (← compileExpr fields a)
      let b' ← liftExcept <| asUInt256 (← compileExpr fields b)
      return ⟨Ty.uint256, TExpr.mod a' b'⟩
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
      | ⟨Ty.address, aExpr⟩, ⟨Ty.uint256, bExpr⟩ => return ⟨Ty.bool, TExpr.eq (TExpr.addrToUint aExpr) bExpr⟩
      | ⟨Ty.uint256, aExpr⟩, ⟨Ty.address, bExpr⟩ => return ⟨Ty.bool, TExpr.eq aExpr (TExpr.addrToUint bExpr)⟩
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
          | Ty.address, ⟨Ty.address, expr⟩ => do
              liftExcept <| ensureTypedIRAddressFieldSupported fieldName field
              emit (.setStorageAddr slot expr)
          | expectedTy, ⟨actualTy, _⟩ =>
              throw s!"Typed IR compile error: setStorage type mismatch for '{fieldName}' (expected {repr expectedTy}, got {repr actualTy})"
  | .setStorageAddr fieldName value => do
      let rhs ← compileExpr fields value
      match findFieldWithResolvedSlot fields fieldName with
      | none =>
          throw s!"Typed IR compile error: unknown storage field '{fieldName}'"
      | some (field, slot) =>
          match (← fieldTypeToTy field.ty), rhs with
          | Ty.address, ⟨Ty.address, expr⟩ => do
              liftExcept <| ensureTypedIRAddressFieldSupported fieldName field
              emit (.setStorageAddr slot expr)
          | Ty.uint256, _ =>
              throw s!"Typed IR compile error: setStorageAddr requires an address-typed field '{fieldName}'"
          | expectedTy, ⟨actualTy, _⟩ =>
              throw s!"Typed IR compile error: setStorageAddr type mismatch for '{fieldName}' (expected {repr expectedTy}, got {repr actualTy})"
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
  | .emit eventName args => do
      -- Event payload words are modeled as indexed topics in typed mode.
      if args.length > 3 then
        throw s!"Typed IR compile error: emit supports at most 3 arguments in typed mode, got {args.length}"
      let argTopicExprs ← args.mapM (fun arg => do
        let argExpr ← compileExpr fields arg
        liftExcept <| asUInt256 argExpr)
      emit (.emit eventName argTopicExprs)
  | .rawLog topics dataOffset dataSize => do
      if topics.length > 4 then
        throw s!"Typed IR compile error: rawLog supports at most 4 topics, got {topics.length}"
      let topicExprs ← topics.mapM (fun t => do
        let tExpr ← compileExpr fields t
        liftExcept <| asUInt256 tExpr)
      let offsetExpr ← liftExcept <| asUInt256 (← compileExpr fields dataOffset)
      let sizeExpr ← liftExcept <| asUInt256 (← compileExpr fields dataSize)
      emit (.rawLog topicExprs offsetExpr sizeExpr)
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

example : paramTypeToTy (ParamType.tuple [ParamType.address, ParamType.uint256]) = Except.ok Ty.uint256 := rfl

example : paramTypeToTy ParamType.bytes = Except.ok Ty.uint256 := rfl

example : paramTypeToTy (ParamType.fixedArray ParamType.uint256 3) = Except.ok Ty.uint256 := rfl

example : paramTypeToTy (ParamType.array ParamType.address) = Except.ok Ty.uint256 := rfl

example : paramTypeToTy ParamType.string = Except.ok Ty.uint256 := rfl

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

/-- Single-statement compilation shape for a broader supported branch subset:
`ite (eq (literal n) (literal m))
     [setStorage fieldName (literal thenVal)]
     [return (literal elseVal)]`
lowers to one typed `if_` with heterogeneous `setStorage`/`return` branches,
from an empty compile state. -/
theorem compileStmts_single_ite_eq_setStorage_then_return_literal_run
    (fields : List Field) (fieldName : String) (slot : Nat)
    (n m thenVal elseVal : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    (compileStmts fields
      [Stmt.ite
        (Expr.eq (Expr.literal n) (Expr.literal m))
        [Stmt.setStorage fieldName (Expr.literal thenVal)]
        [Stmt.return (Expr.literal elseVal)] ]).run {} =
      Except.ok ((),
        { nextId := 0
          vars := []
          params := #[]
          locals := #[]
          body := #[
            TStmt.if_
              (TExpr.eq (TExpr.uintLit n) (TExpr.uintLit m))
              [TStmt.setStorage slot (TExpr.uintLit thenVal)]
              [TStmt.returnUint (TExpr.uintLit elseVal)]
          ] }) := by
  simp [compileStmts, compileStmt, compileExpr, compileBranch, fieldTypeToTy, hfind, emit]
  rfl

/-- Single-statement compilation shape for a broader supported branch subset:
`ite (eq (literal n) (literal m))
     [return (literal thenVal)]
     [setStorage fieldName (literal elseVal)]`
lowers to one typed `if_` with heterogeneous `return`/`setStorage` branches,
from an empty compile state. -/
theorem compileStmts_single_ite_eq_return_then_setStorage_literal_run
    (fields : List Field) (fieldName : String) (slot : Nat)
    (n m thenVal elseVal : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    (compileStmts fields
      [Stmt.ite
        (Expr.eq (Expr.literal n) (Expr.literal m))
        [Stmt.return (Expr.literal thenVal)]
        [Stmt.setStorage fieldName (Expr.literal elseVal)] ]).run {} =
      Except.ok ((),
        { nextId := 0
          vars := []
          params := #[]
          locals := #[]
          body := #[
            TStmt.if_
              (TExpr.eq (TExpr.uintLit n) (TExpr.uintLit m))
              [TStmt.returnUint (TExpr.uintLit thenVal)]
              [TStmt.setStorage slot (TExpr.uintLit elseVal)]
          ] }) := by
  simp [compileStmts, compileStmt, compileExpr, compileBranch, fieldTypeToTy, hfind, emit]
  rfl

/-- Single-statement compilation shape for a broader supported branch subset:
`ite (eq (literal n) (literal m))
     [return (literal thenVal)]
     [return (literal elseVal)]`
lowers to one typed `if_` with two typed `returnUint` branches, from an empty
compile state. -/
theorem compileStmts_single_ite_eq_return_literals_run
    (fields : List Field) (n m thenVal elseVal : Nat) :
    (compileStmts fields
      [Stmt.ite
        (Expr.eq (Expr.literal n) (Expr.literal m))
        [Stmt.return (Expr.literal thenVal)]
        [Stmt.return (Expr.literal elseVal)] ]).run {} =
      Except.ok ((),
        { nextId := 0
          vars := []
          params := #[]
          locals := #[]
          body := #[
            TStmt.if_
              (TExpr.eq (TExpr.uintLit n) (TExpr.uintLit m))
              [TStmt.returnUint (TExpr.uintLit thenVal)]
              [TStmt.returnUint (TExpr.uintLit elseVal)]
          ] }) := by
  simp [compileStmts, compileStmt, compileExpr, compileBranch, emit]
  rfl

/-- Single-statement compilation shape for a broader supported nested-branch subset:
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [return (literal thenVal)]
          [return (literal elseVal)]]
     [return (literal outerElseVal)]`
lowers to one typed outer `if_` whose true branch contains a typed inner `if_`
and whose false branch returns directly, from an empty compile state. -/
theorem compileStmts_single_ite_eq_then_ite_eq_return_literals_run
    (fields : List Field) (n m p q thenVal elseVal outerElseVal : Nat) :
    (compileStmts fields
      [Stmt.ite
        (Expr.eq (Expr.literal n) (Expr.literal m))
        [Stmt.ite
          (Expr.eq (Expr.literal p) (Expr.literal q))
          [Stmt.return (Expr.literal thenVal)]
          [Stmt.return (Expr.literal elseVal)]]
        [Stmt.return (Expr.literal outerElseVal)] ]).run {} =
      Except.ok ((),
        { nextId := 0
          vars := []
          params := #[]
          locals := #[]
          body := #[
            TStmt.if_
              (TExpr.eq (TExpr.uintLit n) (TExpr.uintLit m))
              [TStmt.if_
                (TExpr.eq (TExpr.uintLit p) (TExpr.uintLit q))
                [TStmt.returnUint (TExpr.uintLit thenVal)]
                [TStmt.returnUint (TExpr.uintLit elseVal)]]
              [TStmt.returnUint (TExpr.uintLit outerElseVal)]
          ] }) := by
  simp [compileStmts, compileStmt, compileExpr, compileBranch, emit]
  rfl

/-- Single-statement compilation shape for a broader supported nested-branch subset:
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [setStorage fieldName (literal thenVal)]
          [setStorage fieldName (literal elseVal)]]
     [return (literal outerElseVal)]`
lowers to one typed outer `if_` whose true branch contains a typed inner `if_`
with storage writes and whose false branch returns directly, from an empty
compile state. -/
theorem compileStmts_single_ite_eq_then_ite_eq_setStorage_literals_then_return_literal_run
    (fields : List Field) (fieldName : String) (slot : Nat)
    (n m p q thenVal elseVal outerElseVal : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    (compileStmts fields
      [Stmt.ite
        (Expr.eq (Expr.literal n) (Expr.literal m))
        [Stmt.ite
          (Expr.eq (Expr.literal p) (Expr.literal q))
          [Stmt.setStorage fieldName (Expr.literal thenVal)]
          [Stmt.setStorage fieldName (Expr.literal elseVal)]]
        [Stmt.return (Expr.literal outerElseVal)] ]).run {} =
      Except.ok ((),
        { nextId := 0
          vars := []
          params := #[]
          locals := #[]
          body := #[
            TStmt.if_
              (TExpr.eq (TExpr.uintLit n) (TExpr.uintLit m))
              [TStmt.if_
                (TExpr.eq (TExpr.uintLit p) (TExpr.uintLit q))
                [TStmt.setStorage slot (TExpr.uintLit thenVal)]
                [TStmt.setStorage slot (TExpr.uintLit elseVal)]]
              [TStmt.returnUint (TExpr.uintLit outerElseVal)]
          ] }) := by
  simp [compileStmts, compileStmt, compileExpr, compileBranch, fieldTypeToTy, hfind, emit]
  rfl

/-- Single-statement compilation shape for a broader supported nested heterogeneous branch subset:
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [return (literal thenVal)]
          [return (literal elseVal)]]
     [setStorage fieldName (literal outerElseVal)]`
lowers to one typed outer `if_` whose true branch contains a typed inner `if_`
and whose false branch writes storage directly, from an empty compile state. -/
theorem compileStmts_single_ite_eq_then_ite_eq_return_literals_then_setStorage_literal_run
    (fields : List Field) (fieldName : String) (slot : Nat)
    (n m p q thenVal elseVal outerElseVal : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    (compileStmts fields
      [Stmt.ite
        (Expr.eq (Expr.literal n) (Expr.literal m))
        [Stmt.ite
          (Expr.eq (Expr.literal p) (Expr.literal q))
          [Stmt.return (Expr.literal thenVal)]
          [Stmt.return (Expr.literal elseVal)]]
        [Stmt.setStorage fieldName (Expr.literal outerElseVal)] ]).run {} =
      Except.ok ((),
        { nextId := 0
          vars := []
          params := #[]
          locals := #[]
          body := #[
            TStmt.if_
              (TExpr.eq (TExpr.uintLit n) (TExpr.uintLit m))
              [TStmt.if_
                (TExpr.eq (TExpr.uintLit p) (TExpr.uintLit q))
                [TStmt.returnUint (TExpr.uintLit thenVal)]
                [TStmt.returnUint (TExpr.uintLit elseVal)]]
              [TStmt.setStorage slot (TExpr.uintLit outerElseVal)]
          ] }) := by
  simp [compileStmts, compileStmt, compileExpr, compileBranch, fieldTypeToTy, hfind, emit]
  rfl

/-- Single-statement compilation shape for a broader supported nested heterogeneous branch subset:
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [return (literal thenVal)]
          [return (literal elseVal)]]
     [setStorage fieldName (literal outerElseWriteVal);
      return (literal outerElseRetVal)]`
lowers to one typed outer `if_` whose true branch contains a typed inner `if_`
and whose false branch performs storage write then return, from an empty compile
state. -/
theorem compileStmts_single_ite_eq_then_ite_eq_return_literals_then_setStorage_literal_then_return_literal_run
    (fields : List Field) (fieldName : String) (slot : Nat)
    (n m p q thenVal elseVal outerElseWriteVal outerElseRetVal : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    (compileStmts fields
      [Stmt.ite
        (Expr.eq (Expr.literal n) (Expr.literal m))
        [Stmt.ite
          (Expr.eq (Expr.literal p) (Expr.literal q))
          [Stmt.return (Expr.literal thenVal)]
          [Stmt.return (Expr.literal elseVal)]]
        [Stmt.setStorage fieldName (Expr.literal outerElseWriteVal),
         Stmt.return (Expr.literal outerElseRetVal)] ]).run {} =
      Except.ok ((),
        { nextId := 0
          vars := []
          params := #[]
          locals := #[]
          body := #[
            TStmt.if_
              (TExpr.eq (TExpr.uintLit n) (TExpr.uintLit m))
              [TStmt.if_
                (TExpr.eq (TExpr.uintLit p) (TExpr.uintLit q))
                [TStmt.returnUint (TExpr.uintLit thenVal)]
                [TStmt.returnUint (TExpr.uintLit elseVal)]]
              [TStmt.setStorage slot (TExpr.uintLit outerElseWriteVal),
               TStmt.returnUint (TExpr.uintLit outerElseRetVal)]
          ] }) := by
  simp [compileStmts, compileStmt, compileExpr, compileBranch, fieldTypeToTy, hfind, emit]
  rfl

/-- Single-statement compilation shape for a broader supported nested storage branch subset:
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [setStorage fieldName (literal thenVal)]
          [setStorage fieldName (literal elseVal)]]
     [setStorage fieldName (literal outerElseVal)]`
lowers to one typed outer `if_` whose true branch contains a typed inner `if_`
with storage writes and whose false branch writes storage directly, from an
empty compile state. -/
theorem compileStmts_single_ite_eq_then_ite_eq_setStorage_literals_then_setStorage_literal_run
    (fields : List Field) (fieldName : String) (slot : Nat)
    (n m p q thenVal elseVal outerElseVal : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    (compileStmts fields
      [Stmt.ite
        (Expr.eq (Expr.literal n) (Expr.literal m))
        [Stmt.ite
          (Expr.eq (Expr.literal p) (Expr.literal q))
          [Stmt.setStorage fieldName (Expr.literal thenVal)]
          [Stmt.setStorage fieldName (Expr.literal elseVal)]]
        [Stmt.setStorage fieldName (Expr.literal outerElseVal)] ]).run {} =
      Except.ok ((),
        { nextId := 0
          vars := []
          params := #[]
          locals := #[]
          body := #[
            TStmt.if_
              (TExpr.eq (TExpr.uintLit n) (TExpr.uintLit m))
              [TStmt.if_
                (TExpr.eq (TExpr.uintLit p) (TExpr.uintLit q))
                [TStmt.setStorage slot (TExpr.uintLit thenVal)]
                [TStmt.setStorage slot (TExpr.uintLit elseVal)]]
              [TStmt.setStorage slot (TExpr.uintLit outerElseVal)]
          ] }) := by
  simp [compileStmts, compileStmt, compileExpr, compileBranch, fieldTypeToTy, hfind, emit]
  rfl

/-- Single-statement compilation shape for a broader supported nested heterogeneous branch subset:
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [setStorage fieldName (literal thenVal)]
          [return (literal elseVal)]]
     [return (literal outerElseVal)]`
lowers to one typed outer `if_` whose true branch contains a typed inner `if_`
with heterogeneous `setStorage`/`return` branches and whose false branch
returns directly, from an empty compile state. -/
theorem compileStmts_single_ite_eq_then_ite_eq_setStorage_then_return_literal_then_return_literal_run
    (fields : List Field) (fieldName : String) (slot : Nat)
    (n m p q thenVal elseVal outerElseVal : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    (compileStmts fields
      [Stmt.ite
        (Expr.eq (Expr.literal n) (Expr.literal m))
        [Stmt.ite
          (Expr.eq (Expr.literal p) (Expr.literal q))
          [Stmt.setStorage fieldName (Expr.literal thenVal)]
          [Stmt.return (Expr.literal elseVal)]]
        [Stmt.return (Expr.literal outerElseVal)] ]).run {} =
      Except.ok ((),
        { nextId := 0
          vars := []
          params := #[]
          locals := #[]
          body := #[
            TStmt.if_
              (TExpr.eq (TExpr.uintLit n) (TExpr.uintLit m))
              [TStmt.if_
                (TExpr.eq (TExpr.uintLit p) (TExpr.uintLit q))
                [TStmt.setStorage slot (TExpr.uintLit thenVal)]
                [TStmt.returnUint (TExpr.uintLit elseVal)]]
              [TStmt.returnUint (TExpr.uintLit outerElseVal)]
          ] }) := by
  simp [compileStmts, compileStmt, compileExpr, compileBranch, fieldTypeToTy, hfind, emit]
  rfl

/-- Single-statement compilation shape for a broader supported nested heterogeneous branch subset:
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [setStorage fieldName (literal thenVal)]
          [return (literal elseVal)]]
     [setStorage fieldName (literal outerElseVal)]`
lowers to one typed outer `if_` whose true branch contains a typed inner `if_`
with heterogeneous `setStorage`/`return` branches and whose false branch
writes storage directly, from an empty compile state. -/
theorem compileStmts_single_ite_eq_then_ite_eq_setStorage_then_return_literal_then_setStorage_literal_run
    (fields : List Field) (fieldName : String) (slot : Nat)
    (n m p q thenVal elseVal outerElseVal : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    (compileStmts fields
      [Stmt.ite
        (Expr.eq (Expr.literal n) (Expr.literal m))
        [Stmt.ite
          (Expr.eq (Expr.literal p) (Expr.literal q))
          [Stmt.setStorage fieldName (Expr.literal thenVal)]
          [Stmt.return (Expr.literal elseVal)]]
        [Stmt.setStorage fieldName (Expr.literal outerElseVal)] ]).run {} =
      Except.ok ((),
        { nextId := 0
          vars := []
          params := #[]
          locals := #[]
          body := #[
            TStmt.if_
              (TExpr.eq (TExpr.uintLit n) (TExpr.uintLit m))
              [TStmt.if_
                (TExpr.eq (TExpr.uintLit p) (TExpr.uintLit q))
                [TStmt.setStorage slot (TExpr.uintLit thenVal)]
                [TStmt.returnUint (TExpr.uintLit elseVal)]]
              [TStmt.setStorage slot (TExpr.uintLit outerElseVal)]
          ] }) := by
  simp [compileStmts, compileStmt, compileExpr, compileBranch, fieldTypeToTy, hfind, emit]
  rfl

/-- Single-statement compilation shape for a broader supported nested heterogeneous branch subset:
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [return (literal thenVal)]
          [setStorage fieldName (literal elseVal)]]
     [return (literal outerElseVal)]`
lowers to one typed outer `if_` whose true branch contains a typed inner `if_`
with heterogeneous `return`/`setStorage` branches and whose false branch
returns directly, from an empty compile state. -/
theorem compileStmts_single_ite_eq_then_ite_eq_return_then_setStorage_literal_then_return_literal_run
    (fields : List Field) (fieldName : String) (slot : Nat)
    (n m p q thenVal elseVal outerElseVal : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    (compileStmts fields
      [Stmt.ite
        (Expr.eq (Expr.literal n) (Expr.literal m))
        [Stmt.ite
          (Expr.eq (Expr.literal p) (Expr.literal q))
          [Stmt.return (Expr.literal thenVal)]
          [Stmt.setStorage fieldName (Expr.literal elseVal)]]
        [Stmt.return (Expr.literal outerElseVal)] ]).run {} =
      Except.ok ((),
        { nextId := 0
          vars := []
          params := #[]
          locals := #[]
          body := #[
            TStmt.if_
              (TExpr.eq (TExpr.uintLit n) (TExpr.uintLit m))
              [TStmt.if_
                (TExpr.eq (TExpr.uintLit p) (TExpr.uintLit q))
                [TStmt.returnUint (TExpr.uintLit thenVal)]
                [TStmt.setStorage slot (TExpr.uintLit elseVal)]]
              [TStmt.returnUint (TExpr.uintLit outerElseVal)]
          ] }) := by
  simp [compileStmts, compileStmt, compileExpr, compileBranch, fieldTypeToTy, hfind, emit]
  rfl

/-- Single-statement compilation shape for a broader supported nested heterogeneous branch subset:
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [return (literal thenVal)]
          [setStorage fieldName (literal elseVal)]]
     [setStorage fieldName (literal outerElseVal)]`
lowers to one typed outer `if_` whose true branch contains a typed inner `if_`
with heterogeneous `return`/`setStorage` branches and whose false branch
writes storage directly, from an empty compile state. -/
theorem compileStmts_single_ite_eq_then_ite_eq_return_then_setStorage_literal_then_setStorage_literal_run
    (fields : List Field) (fieldName : String) (slot : Nat)
    (n m p q thenVal elseVal outerElseVal : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    (compileStmts fields
      [Stmt.ite
        (Expr.eq (Expr.literal n) (Expr.literal m))
        [Stmt.ite
          (Expr.eq (Expr.literal p) (Expr.literal q))
          [Stmt.return (Expr.literal thenVal)]
          [Stmt.setStorage fieldName (Expr.literal elseVal)]]
        [Stmt.setStorage fieldName (Expr.literal outerElseVal)] ]).run {} =
      Except.ok ((),
        { nextId := 0
          vars := []
          params := #[]
          locals := #[]
          body := #[
            TStmt.if_
              (TExpr.eq (TExpr.uintLit n) (TExpr.uintLit m))
              [TStmt.if_
                (TExpr.eq (TExpr.uintLit p) (TExpr.uintLit q))
                [TStmt.returnUint (TExpr.uintLit thenVal)]
                [TStmt.setStorage slot (TExpr.uintLit elseVal)]]
              [TStmt.setStorage slot (TExpr.uintLit outerElseVal)]
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
`require (logicalNot (eq (literal n) (literal m))) message`
lowers to one typed `if_` with guard `not (eq ...)` and an else-branch `revert`,
from an empty compile state. -/
theorem compileStmts_single_require_not_eq_literals_run
    (fields : List Field) (message : String) (n m : Nat) :
    (compileStmts fields
      [Stmt.require (Expr.logicalNot (Expr.eq (Expr.literal n) (Expr.literal m))) message]).run {} =
      Except.ok ((),
        { nextId := 0
          vars := []
          params := #[]
          locals := #[]
          body := #[
            TStmt.if_
              (TExpr.not (TExpr.eq (TExpr.uintLit n) (TExpr.uintLit m)))
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

/-- Single-statement compilation shape for a broader supported require subset:
`require (gt (literal n) (literal m)) message`
lowers to one typed `if_` with guard `lt m n` and an else-branch `revert`,
from an empty compile state. -/
theorem compileStmts_single_require_gt_literals_run
    (fields : List Field) (message : String) (n m : Nat) :
    (compileStmts fields
      [Stmt.require (Expr.gt (Expr.literal n) (Expr.literal m)) message]).run {} =
      Except.ok ((),
        { nextId := 0
          vars := []
          params := #[]
          locals := #[]
          body := #[
            TStmt.if_
              (TExpr.lt (TExpr.uintLit m) (TExpr.uintLit n))
              []
              [TStmt.revert message]
          ] }) := by
  simp [compileStmts, compileStmt, compileExpr, emit]
  rfl

/-- Single-statement compilation shape for a broader supported require subset:
`require (ge (literal n) (literal m)) message`
lowers to one typed `if_` with guard `not (lt ...)` and an else-branch `revert`,
from an empty compile state. -/
theorem compileStmts_single_require_ge_literals_run
    (fields : List Field) (message : String) (n m : Nat) :
    (compileStmts fields
      [Stmt.require (Expr.ge (Expr.literal n) (Expr.literal m)) message]).run {} =
      Except.ok ((),
        { nextId := 0
          vars := []
          params := #[]
          locals := #[]
          body := #[
            TStmt.if_
              (TExpr.not (TExpr.lt (TExpr.uintLit n) (TExpr.uintLit m)))
              []
              [TStmt.revert message]
          ] }) := by
  simp [compileStmts, compileStmt, compileExpr, emit]
  rfl

/-- Single-statement compilation shape for a broader supported require subset:
`require (le (literal n) (literal m)) message`
lowers to one typed `if_` with guard `not (lt m n)` and an else-branch `revert`,
from an empty compile state. -/
theorem compileStmts_single_require_le_literals_run
    (fields : List Field) (message : String) (n m : Nat) :
    (compileStmts fields
      [Stmt.require (Expr.le (Expr.literal n) (Expr.literal m)) message]).run {} =
      Except.ok ((),
        { nextId := 0
          vars := []
          params := #[]
          locals := #[]
          body := #[
            TStmt.if_
              (TExpr.not (TExpr.lt (TExpr.uintLit m) (TExpr.uintLit n)))
              []
              [TStmt.revert message]
          ] }) := by
  simp [compileStmts, compileStmt, compileExpr, emit]
  rfl

/-- Single-statement compilation shape for a broader supported require subset:
`require (logicalAnd (eq (literal n) (literal m)) (lt (literal p) (literal q))) message`
lowers to one typed `if_` with an else-branch `revert`, from an empty compile state. -/
theorem compileStmts_single_require_and_eq_lt_literals_run
    (fields : List Field) (message : String) (n m p q : Nat) :
    (compileStmts fields
      [Stmt.require
        (Expr.logicalAnd
          (Expr.eq (Expr.literal n) (Expr.literal m))
          (Expr.lt (Expr.literal p) (Expr.literal q)))
        message]).run {} =
      Except.ok ((),
        { nextId := 0
          vars := []
          params := #[]
          locals := #[]
          body := #[
            TStmt.if_
              (TExpr.and
                (TExpr.eq (TExpr.uintLit n) (TExpr.uintLit m))
                (TExpr.lt (TExpr.uintLit p) (TExpr.uintLit q)))
              []
              [TStmt.revert message]
          ] }) := by
  simp [compileStmts, compileStmt, compileExpr, emit]
  rfl

/-- Single-statement compilation shape for a broader supported require subset:
`require (logicalOr (eq (literal n) (literal m)) (lt (literal p) (literal q))) message`
lowers to one typed `if_` with an else-branch `revert`, from an empty compile state. -/
theorem compileStmts_single_require_or_eq_lt_literals_run
    (fields : List Field) (message : String) (n m p q : Nat) :
    (compileStmts fields
      [Stmt.require
        (Expr.logicalOr
          (Expr.eq (Expr.literal n) (Expr.literal m))
          (Expr.lt (Expr.literal p) (Expr.literal q)))
        message]).run {} =
      Except.ok ((),
        { nextId := 0
          vars := []
          params := #[]
          locals := #[]
          body := #[
            TStmt.if_
              (TExpr.or
                (TExpr.eq (TExpr.uintLit n) (TExpr.uintLit m))
                (TExpr.lt (TExpr.uintLit p) (TExpr.uintLit q)))
              []
              [TStmt.revert message]
          ] }) := by
  simp [compileStmts, compileStmt, compileExpr, emit]
  rfl

/-- Three-statement compilation shape for Counter.increment pattern:
`letVar tmp (storage field); setStorage field (add (localVar tmp) (literal m)); stop`
lowers to one SSA `let_` (from getStorage), one `setStorage` (with add), and one `stop`. -/
theorem compileStmts_let_storage_setStorage_add_local_stop_run
    (fields : List Field) (fieldName tmp : String) (slot : Nat) (m : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    (compileStmts fields
      [ Stmt.letVar tmp (Expr.storage fieldName)
      , Stmt.setStorage fieldName (Expr.add (Expr.localVar tmp) (Expr.literal m))
      , Stmt.stop
      ]).run {} =
      Except.ok ((),
        { nextId := 1
          vars := [(tmp, { id := 0, ty := Ty.uint256 })]
          params := #[]
          locals := #[{ id := 0, ty := Ty.uint256 }]
          body := #[
            TStmt.let_ { id := 0, ty := Ty.uint256 } (TExpr.getStorage slot),
            TStmt.setStorage slot
              (TExpr.add (TExpr.var { id := 0, ty := Ty.uint256 }) (TExpr.uintLit m)),
            TStmt.stop
          ] }) := by
  simp [compileStmts, compileStmt, compileExpr, compileStorageRead, emitSSABind, freshVar,
    bindVar, pushLocal, lookupVar, fieldTypeToTy, hfind, emit]
  rfl

/-- Three-statement compilation shape for Counter.decrement pattern:
`letVar tmp (storage field); setStorage field (sub (localVar tmp) (literal m)); stop`
lowers to one SSA `let_` (from getStorage), one `setStorage` (with sub), and one `stop`. -/
theorem compileStmts_let_storage_setStorage_sub_local_stop_run
    (fields : List Field) (fieldName tmp : String) (slot : Nat) (m : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    (compileStmts fields
      [ Stmt.letVar tmp (Expr.storage fieldName)
      , Stmt.setStorage fieldName (Expr.sub (Expr.localVar tmp) (Expr.literal m))
      , Stmt.stop
      ]).run {} =
      Except.ok ((),
        { nextId := 1
          vars := [(tmp, { id := 0, ty := Ty.uint256 })]
          params := #[]
          locals := #[{ id := 0, ty := Ty.uint256 }]
          body := #[
            TStmt.let_ { id := 0, ty := Ty.uint256 } (TExpr.getStorage slot),
            TStmt.setStorage slot
              (TExpr.sub (TExpr.var { id := 0, ty := Ty.uint256 }) (TExpr.uintLit m)),
            TStmt.stop
          ] }) := by
  simp [compileStmts, compileStmt, compileExpr, compileStorageRead, emitSSABind, freshVar,
    bindVar, pushLocal, lookupVar, fieldTypeToTy, hfind, emit]
  rfl

/-- Three-statement compilation shape for timestamp-write pattern:
`letVar tmp blockTimestamp; setStorage field (localVar tmp); stop`
lowers to one SSA `let_` (from `timestamp()`), one `setStorage`, and one `stop`. -/
theorem compileStmts_let_blockTimestamp_setStorage_local_stop_run
    (fields : List Field) (fieldName tmp : String) (slot : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    (compileStmts fields
      [ Stmt.letVar tmp Expr.blockTimestamp
      , Stmt.setStorage fieldName (Expr.localVar tmp)
      , Stmt.stop
      ]).run {} =
      Except.ok ((),
        { nextId := 1
          vars := [(tmp, { id := 0, ty := Ty.uint256 })]
          params := #[]
          locals := #[{ id := 0, ty := Ty.uint256 }]
          body := #[
            TStmt.let_ { id := 0, ty := Ty.uint256 } TExpr.blockTimestamp,
            TStmt.setStorage slot
              (TExpr.var { id := 0, ty := Ty.uint256 }),
            TStmt.stop
          ] }) := by
  simp [compileStmts, compileStmt, compileExpr, emitSSABind, freshVar,
    bindVar, pushLocal, lookupVar, fieldTypeToTy, hfind, emit]
  rfl

/-- Two-statement compilation shape for Counter.getCount pattern:
`letVar tmp (storage field); return (localVar tmp)`
lowers to one SSA `let_` (from getStorage) and one typed `returnUint`. -/
theorem compileStmts_let_storage_return_local_run
    (fields : List Field) (fieldName tmp : String) (slot : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    (compileStmts fields
      [ Stmt.letVar tmp (Expr.storage fieldName)
      , Stmt.return (Expr.localVar tmp)
      ]).run {} =
      Except.ok ((),
        { nextId := 1
          vars := [(tmp, { id := 0, ty := Ty.uint256 })]
          params := #[]
          locals := #[{ id := 0, ty := Ty.uint256 }]
          body := #[
            TStmt.let_ { id := 0, ty := Ty.uint256 } (TExpr.getStorage slot),
            TStmt.returnUint (TExpr.var { id := 0, ty := Ty.uint256 })
          ] }) := by
  simp [compileStmts, compileStmt, compileExpr, compileStorageRead, emitSSABind, freshVar,
    bindVar, pushLocal, lookupVar, fieldTypeToTy, hfind, emit]
  rfl

/-- Single-statement compilation shape for direct storage return (uint256):
`return (storage fieldName)` lowers to one typed `returnUint (getStorage slot)`. -/
theorem compileStmts_single_return_storage_run
    (fields : List Field) (fieldName : String) (slot : Nat)
    (st : CompileState)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    (compileStmts fields [Stmt.return (Expr.storage fieldName)]).run st =
      Except.ok ((), { st with body := st.body.push (TStmt.returnUint (TExpr.getStorage slot)) }) := by
  simp [compileStmts, compileStmt, compileExpr, compileStorageRead, fieldTypeToTy, hfind, emit]
  rfl

/-- Single-statement compilation shape for direct storage return (address):
`return (storage fieldName)` lowers to one typed `returnAddr (getStorageAddr slot)`. -/
theorem compileStmts_single_return_storage_addr_run
    (fields : List Field) (fieldName : String) (slot : Nat)
    (st : CompileState)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.address }, slot)) :
    (compileStmts fields [Stmt.return (Expr.storage fieldName)]).run st =
      Except.ok ((), { st with body := st.body.push (TStmt.returnAddr (TExpr.getStorageAddr slot)) }) := by
  simp [compileStmts, compileStmt, compileExpr, compileStorageRead, fieldTypeToTy, hfind, emit]
  rfl

/-- Compilation shape for `require (eq caller (storage ownerField)) msg ; setStorage countField (add (storage countField) (literal n)) ; stop`.
This pattern is used by OwnedCounter.increment. -/
theorem compileStmts_require_caller_eq_storage_addr_setStorage_add_storage_literal_stop_run
    (fields : List Field) (ownerField countField msg : String)
    (ownerSlot countSlot : Nat) (n : Nat)
    (hOwner : findFieldWithResolvedSlot fields ownerField =
      some ({ name := ownerField, ty := FieldType.address }, ownerSlot))
    (hCount : findFieldWithResolvedSlot fields countField =
      some ({ name := countField, ty := FieldType.uint256 }, countSlot)) :
    (compileStmts fields
      [ Stmt.require (Expr.eq Expr.caller (Expr.storage ownerField)) msg
      , Stmt.setStorage countField (Expr.add (Expr.storage countField) (Expr.literal n))
      , Stmt.stop ]).run {} =
      Except.ok ((),
        { nextId := 0
          vars := []
          params := #[]
          locals := #[]
          body := #[
            TStmt.if_ (TExpr.eq TExpr.sender (TExpr.getStorageAddr ownerSlot)) [] [TStmt.revert msg],
            TStmt.setStorage countSlot (TExpr.add (TExpr.getStorage countSlot) (TExpr.uintLit n)),
            TStmt.stop
          ] }) := by
  simp [compileStmts, compileStmt, compileExpr, compileStorageRead, fieldTypeToTy,
    hOwner, hCount, asBool, asUInt256, liftExcept, emit]
  rfl

/-- Compilation shape for `require (eq caller (storage ownerField)) msg ; setStorage countField (sub (storage countField) (literal n)) ; stop`.
This pattern is used by OwnedCounter.decrement. -/
theorem compileStmts_require_caller_eq_storage_addr_setStorage_sub_storage_literal_stop_run
    (fields : List Field) (ownerField countField msg : String)
    (ownerSlot countSlot : Nat) (n : Nat)
    (hOwner : findFieldWithResolvedSlot fields ownerField =
      some ({ name := ownerField, ty := FieldType.address }, ownerSlot))
    (hCount : findFieldWithResolvedSlot fields countField =
      some ({ name := countField, ty := FieldType.uint256 }, countSlot)) :
    (compileStmts fields
      [ Stmt.require (Expr.eq Expr.caller (Expr.storage ownerField)) msg
      , Stmt.setStorage countField (Expr.sub (Expr.storage countField) (Expr.literal n))
      , Stmt.stop ]).run {} =
      Except.ok ((),
        { nextId := 0
          vars := []
          params := #[]
          locals := #[]
          body := #[
            TStmt.if_ (TExpr.eq TExpr.sender (TExpr.getStorageAddr ownerSlot)) [] [TStmt.revert msg],
            TStmt.setStorage countSlot (TExpr.sub (TExpr.getStorage countSlot) (TExpr.uintLit n)),
            TStmt.stop
          ] }) := by
  simp [compileStmts, compileStmt, compileExpr, compileStorageRead, fieldTypeToTy,
    hOwner, hCount, asBool, asUInt256, liftExcept, emit]
  rfl

/-- Single-statement compilation shape for mapping return with caller key:
`return (mapping fieldName caller)` lowers to `returnUint (getMapping slot sender)`. -/
theorem compileStmts_single_return_mapping_caller_run
    (fields : List Field) (fieldName : String) (slot : Nat)
    (st : CompileState)
    (hSlot : findFieldSlot fields fieldName = some slot) :
    (compileStmts fields [Stmt.return (Expr.mapping fieldName Expr.caller)]).run st =
      Except.ok ((), { st with body := st.body.push (TStmt.returnUint (TExpr.getMapping slot TExpr.sender)) }) := by
  simp [compileStmts, compileStmt, compileExpr, asAddress, hSlot, emit, liftExcept]
  rfl

/-- Two-statement compilation shape for address storage read + return:
`letVar tmp (storage field); return (localVar tmp)` (address variant)
lowers to one SSA `let_` (from getStorageAddr) and one typed `returnAddr`. -/
theorem compileStmts_let_storage_addr_return_local_run
    (fields : List Field) (fieldName tmp : String) (slot : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.address }, slot)) :
    (compileStmts fields
      [ Stmt.letVar tmp (Expr.storage fieldName)
      , Stmt.return (Expr.localVar tmp)
      ]).run {} =
      Except.ok ((),
        { nextId := 1
          vars := [(tmp, { id := 0, ty := Ty.address })]
          params := #[]
          locals := #[{ id := 0, ty := Ty.address }]
          body := #[
            TStmt.let_ { id := 0, ty := Ty.address } (TExpr.getStorageAddr slot),
            TStmt.returnAddr (TExpr.var { id := 0, ty := Ty.address })
          ] }) := by
  simp [compileStmts, compileStmt, compileExpr, compileStorageRead, emitSSABind, freshVar,
    bindVar, pushLocal, lookupVar, fieldTypeToTy, hfind, emit]
  rfl

/-- Helper: lookupVar finds a variable at the head of the vars list. -/
private theorem lookupVar_head (name : String) (v : TVar) (rest : List (String × TVar))
    (st : CompileState) (h : st.vars = (name, v) :: rest) :
    (lookupVar name).run st = Except.ok (v, st) := by
  simp [lookupVar, h]; rfl

/-- Two-statement compilation shape for mapping(param) read + return from 1-param state. -/
theorem compileStmts_let_mapping_param_return_local_run
    (fields : List Field) (fieldName paramName tmp : String) (slot : Nat)
    (hSlot : findFieldSlot fields fieldName = some slot) :
    (compileStmts fields
      [ Stmt.letVar tmp (Expr.mapping fieldName (Expr.param paramName))
      , Stmt.return (Expr.localVar tmp)
      ]).run
      (CompileState.mk 1
        [(paramName, { id := 0, ty := Ty.address })]
        #[{ id := 0, ty := Ty.address }]
        #[] #[]) =
      Except.ok ((),
        { nextId := 2
          vars := [(tmp, { id := 1, ty := Ty.uint256 }),
                   (paramName, { id := 0, ty := Ty.address })]
          params := #[{ id := 0, ty := Ty.address }]
          locals := #[{ id := 1, ty := Ty.uint256 }]
          body := #[
            TStmt.let_ { id := 1, ty := Ty.uint256 }
              (TExpr.getMapping slot (TExpr.var { id := 0, ty := Ty.address })),
            TStmt.returnUint (TExpr.var { id := 1, ty := Ty.uint256 })
          ] }) := by
  simp [compileStmts, compileStmt, compileExpr, emitSSABind, freshVar,
    bindVar, pushLocal, lookupVar, asAddress, liftExcept, hSlot, emit,
    List.find?]; rfl

/-- Two-statement compilation shape for mapping2(param1, param2) read + return from 2-param state. -/
theorem compileStmts_let_mapping2_params_return_local_run
    (fields : List Field) (fieldName p1 p2 tmp : String) (slot : Nat)
    (hSlot : findFieldSlot fields fieldName = some slot)
    (hp : p1 ≠ p2) :
    (compileStmts fields
      [ Stmt.letVar tmp (Expr.mapping2 fieldName (Expr.param p1) (Expr.param p2))
      , Stmt.return (Expr.localVar tmp)
      ]).run
      (CompileState.mk 2
        [(p2, { id := 1, ty := Ty.address }),
         (p1, { id := 0, ty := Ty.address })]
        #[{ id := 0, ty := Ty.address }, { id := 1, ty := Ty.address }]
        #[] #[]) =
      Except.ok ((),
        { nextId := 3
          vars := [(tmp, { id := 2, ty := Ty.uint256 }),
                   (p2, { id := 1, ty := Ty.address }),
                   (p1, { id := 0, ty := Ty.address })]
          params := #[{ id := 0, ty := Ty.address }, { id := 1, ty := Ty.address }]
          locals := #[{ id := 2, ty := Ty.uint256 }]
          body := #[
            TStmt.let_ { id := 2, ty := Ty.uint256 }
              (TExpr.getMapping2 slot
                (TExpr.var { id := 0, ty := Ty.address })
                (TExpr.var { id := 1, ty := Ty.address })),
            TStmt.returnUint (TExpr.var { id := 2, ty := Ty.uint256 })
          ] }) := by
  have hne : (p2 == p1) = false := beq_false_of_ne hp.symm
  simp [compileStmts, compileStmt, compileExpr, emitSSABind, freshVar,
    bindVar, pushLocal, lookupVar, asAddress, liftExcept, hSlot, emit,
    List.find?, hne]; rfl

/-- Three-statement compilation shape for approve pattern. -/
theorem compileStmts_let_caller_setMapping2_stop_run
    (fields : List Field) (fieldName senderVar p1 p2 : String) (slot : Nat)
    (hSlot : findFieldSlot fields fieldName = some slot)
    (h1 : senderVar ≠ p2) (h2 : senderVar ≠ p1) (h3 : p2 ≠ p1)
    (_ : p1 ≠ p2) (_ : p1 ≠ senderVar) (_ : p2 ≠ senderVar) :
    (compileStmts fields
      [ Stmt.letVar senderVar Expr.caller
      , Stmt.setMapping2 fieldName (Expr.localVar senderVar) (Expr.param p1) (Expr.param p2)
      , Stmt.stop
      ]).run
      (CompileState.mk 2
        [(p2, { id := 1, ty := Ty.uint256 }),
         (p1, { id := 0, ty := Ty.address })]
        #[{ id := 0, ty := Ty.address }, { id := 1, ty := Ty.uint256 }]
        #[] #[]) =
      Except.ok ((),
        { nextId := 3
          vars := [(senderVar, { id := 2, ty := Ty.address }),
                   (p2, { id := 1, ty := Ty.uint256 }),
                   (p1, { id := 0, ty := Ty.address })]
          params := #[{ id := 0, ty := Ty.address }, { id := 1, ty := Ty.uint256 }]
          locals := #[{ id := 2, ty := Ty.address }]
          body := #[
            TStmt.let_ { id := 2, ty := Ty.address } TExpr.sender,
            TStmt.setMapping2 slot
              (TExpr.var { id := 2, ty := Ty.address })
              (TExpr.var { id := 0, ty := Ty.address })
              (TExpr.var { id := 1, ty := Ty.uint256 }),
            TStmt.stop
          ] }) := by
  have hne1 : (senderVar == p2) = false := beq_false_of_ne h1
  have hne2 : (senderVar == p1) = false := beq_false_of_ne h2
  have hne3 : (p2 == p1) = false := beq_false_of_ne h3
  simp [compileStmts, compileStmt, compileExpr, emitSSABind, freshVar,
    bindVar, pushLocal, lookupVar, asAddress, asUInt256, liftExcept, hSlot, emit,
    List.find?, hne1, hne2, hne3]; rfl

/-- Two-statement compilation shape for mappingUint(param) read + return from 1-param Uint256 state. -/
theorem compileStmts_let_mappingUint_param_return_local_run
    (fields : List Field) (fieldName paramName tmp : String) (slot : Nat)
    (hSlot : findFieldSlot fields fieldName = some slot) :
    (compileStmts fields
      [ Stmt.letVar tmp (Expr.mappingUint fieldName (Expr.param paramName))
      , Stmt.return (Expr.localVar tmp)
      ]).run
      (CompileState.mk 1
        [(paramName, { id := 0, ty := Ty.uint256 })]
        #[{ id := 0, ty := Ty.uint256 }]
        #[] #[]) =
      Except.ok ((),
        { nextId := 2
          vars := [(tmp, { id := 1, ty := Ty.uint256 }),
                   (paramName, { id := 0, ty := Ty.uint256 })]
          params := #[{ id := 0, ty := Ty.uint256 }]
          locals := #[{ id := 1, ty := Ty.uint256 }]
          body := #[
            TStmt.let_ { id := 1, ty := Ty.uint256 }
              (TExpr.getMappingUint slot (TExpr.var { id := 0, ty := Ty.uint256 })),
            TStmt.returnUint (TExpr.var { id := 1, ty := Ty.uint256 })
          ] }) := by
  simp [compileStmts, compileStmt, compileExpr, emitSSABind, freshVar,
    bindVar, pushLocal, lookupVar, asUInt256, liftExcept, hSlot, emit,
    List.find?]; rfl

/-- Two-statement compilation shape for setMappingUint(param1, param2) + stop from 2-param Uint256 state. -/
theorem compileStmts_setMappingUint_params_stop_run
    (fields : List Field) (fieldName p1 p2 : String) (slot : Nat)
    (hSlot : findFieldSlot fields fieldName = some slot)
    (hp : p1 ≠ p2) :
    (compileStmts fields
      [ Stmt.setMappingUint fieldName (Expr.param p1) (Expr.param p2)
      , Stmt.stop
      ]).run
      (CompileState.mk 2
        [(p2, { id := 1, ty := Ty.uint256 }),
         (p1, { id := 0, ty := Ty.uint256 })]
        #[{ id := 0, ty := Ty.uint256 }, { id := 1, ty := Ty.uint256 }]
        #[] #[]) =
      Except.ok ((),
        { nextId := 2
          vars := [(p2, { id := 1, ty := Ty.uint256 }),
                   (p1, { id := 0, ty := Ty.uint256 })]
          params := #[{ id := 0, ty := Ty.uint256 }, { id := 1, ty := Ty.uint256 }]
          locals := #[]
          body := #[
            TStmt.setMappingUint slot
              (TExpr.var { id := 0, ty := Ty.uint256 })
              (TExpr.var { id := 1, ty := Ty.uint256 }),
            TStmt.stop
          ] }) := by
  have hne : (p2 == p1) = false := beq_false_of_ne hp.symm
  simp [compileStmts, compileStmt, compileExpr,
    lookupVar, asUInt256, liftExcept, hSlot, emit,
    List.find?, hne]; rfl

/-- Compilation shape for the Morpho `setOwner` pattern:
`letVar senderVar caller ; letVar ownerVar (storage ownerField) ;
 require (eq (localVar senderVar) (localVar ownerVar)) msg1 ;
 require (logicalNot (eq (param paramName) (localVar ownerVar))) msg2 ;
 setStorage ownerField (param paramName) ; stop`.
This pattern is used by Morpho Blue's `setOwner` and `setFeeRecipient` admin functions. -/
theorem compileStmts_letCallerLetStorageAddrReqEqReqNeqSetStorageAddrParamStop_run
    (fields : List Field) (ownerField senderVar ownerVar paramName msg1 msg2 : String)
    (ownerSlot : Nat)
    (hOwner : findFieldWithResolvedSlot fields ownerField =
      some ({ name := ownerField, ty := FieldType.address }, ownerSlot))
    (hne_sv_p : senderVar ≠ paramName)
    (hne_ov_p : ownerVar ≠ paramName)
    (hne_ov_sv : ownerVar ≠ senderVar) :
    (compileStmts fields
      [ Stmt.letVar senderVar Expr.caller
      , Stmt.letVar ownerVar (Expr.storage ownerField)
      , Stmt.require (Expr.eq (Expr.localVar senderVar) (Expr.localVar ownerVar)) msg1
      , Stmt.require (Expr.logicalNot (Expr.eq (Expr.param paramName) (Expr.localVar ownerVar))) msg2
      , Stmt.setStorage ownerField (Expr.param paramName)
      , Stmt.stop
      ]).run
      (CompileState.mk 1
        [(paramName, { id := 0, ty := Ty.address })]
        #[{ id := 0, ty := Ty.address }]
        #[] #[]) =
      Except.ok ((),
        { nextId := 3
          vars := [(ownerVar, { id := 2, ty := Ty.address }),
                   (senderVar, { id := 1, ty := Ty.address }),
                   (paramName, { id := 0, ty := Ty.address })]
          params := #[{ id := 0, ty := Ty.address }]
          locals := #[{ id := 1, ty := Ty.address }, { id := 2, ty := Ty.address }]
          body := #[
            TStmt.let_ { id := 1, ty := Ty.address } TExpr.sender,
            TStmt.let_ { id := 2, ty := Ty.address } (TExpr.getStorageAddr ownerSlot),
            TStmt.if_ (TExpr.eq
                (TExpr.var { id := 1, ty := Ty.address })
                (TExpr.var { id := 2, ty := Ty.address }))
              [] [TStmt.revert msg1],
            TStmt.if_ (TExpr.not (TExpr.eq
                (TExpr.var { id := 0, ty := Ty.address })
                (TExpr.var { id := 2, ty := Ty.address })))
              [] [TStmt.revert msg2],
            TStmt.setStorageAddr ownerSlot (TExpr.var { id := 0, ty := Ty.address }),
            TStmt.stop
          ] }) := by
  have h1 : (senderVar == paramName) = false := beq_false_of_ne hne_sv_p
  have h2 : (ownerVar == paramName) = false := beq_false_of_ne hne_ov_p
  have h3 : (ownerVar == senderVar) = false := beq_false_of_ne hne_ov_sv
  have hsr : compileStorageRead fields ownerField =
      Except.ok ⟨Ty.address, TExpr.getStorageAddr ownerSlot⟩ := by
    simp only [compileStorageRead, hOwner, fieldTypeToTy]; rfl
  simp [compileStmts, compileStmt, compileExpr, hsr, hOwner, fieldTypeToTy,
    emitSSABind, freshVar, bindVar, pushLocal, lookupVar, asBool,
    liftExcept, emit, List.find?, h1, h2, h3, monadLift]; rfl

/-- Compilation shape for the Morpho `setFeeRecipient` owner-auth pattern:
`letVar senderVar caller ; letVar ownerVar (storage ownerField) ;
 require (eq (localVar senderVar) (localVar ownerVar)) msg1 ;
 letVar targetVar (storage targetField) ;
 require (logicalNot (eq (param paramName) (localVar targetVar))) msg2 ;
 setStorage targetField (param paramName) ; stop`. -/
def morphoSetFeeRecipientOwnerAuthStmts
    (ownerField targetField senderVar ownerVar targetVar paramName msg1 msg2 : String) : List Stmt :=
  [ Stmt.letVar senderVar Expr.caller
  , Stmt.letVar ownerVar (Expr.storage ownerField)
  , Stmt.require (Expr.eq (Expr.localVar senderVar) (Expr.localVar ownerVar)) msg1
  , Stmt.letVar targetVar (Expr.storage targetField)
  , Stmt.require (Expr.logicalNot (Expr.eq (Expr.param paramName) (Expr.localVar targetVar))) msg2
  , Stmt.setStorage targetField (Expr.param paramName)
  , Stmt.stop
  ]

def morphoSetFeeRecipientOwnerAuthExpectedState
    (ownerSlot targetSlot : Nat)
    (senderVar ownerVar targetVar paramName msg1 msg2 : String) : CompileState :=
  { nextId := 4
    vars := [(targetVar, { id := 3, ty := Ty.address }),
             (ownerVar, { id := 2, ty := Ty.address }),
             (senderVar, { id := 1, ty := Ty.address }),
             (paramName, { id := 0, ty := Ty.address })]
    params := #[{ id := 0, ty := Ty.address }]
    locals := #[{ id := 1, ty := Ty.address }, { id := 2, ty := Ty.address },
                { id := 3, ty := Ty.address }]
    body := #[
      TStmt.let_ { id := 1, ty := Ty.address } TExpr.sender,
      TStmt.let_ { id := 2, ty := Ty.address } (TExpr.getStorageAddr ownerSlot),
      TStmt.if_ (TExpr.eq
          (TExpr.var { id := 1, ty := Ty.address })
          (TExpr.var { id := 2, ty := Ty.address }))
        [] [TStmt.revert msg1],
      TStmt.let_ { id := 3, ty := Ty.address } (TExpr.getStorageAddr targetSlot),
      TStmt.if_ (TExpr.not (TExpr.eq
          (TExpr.var { id := 0, ty := Ty.address })
          (TExpr.var { id := 3, ty := Ty.address })))
        [] [TStmt.revert msg2],
      TStmt.setStorageAddr targetSlot (TExpr.var { id := 0, ty := Ty.address }),
      TStmt.stop
    ] }

theorem compileStmts_letCallerLetStorageAddrReqEqLetStorageAddrReqNeqSetStorageAddrParamStop_run
    (fields : List Field) (ownerField targetField senderVar ownerVar targetVar paramName msg1 msg2 : String)
    (ownerSlot targetSlot : Nat)
    (hOwner : findFieldWithResolvedSlot fields ownerField =
      some ({ name := ownerField, ty := FieldType.address }, ownerSlot))
    (hTarget : findFieldWithResolvedSlot fields targetField =
      some ({ name := targetField, ty := FieldType.address }, targetSlot))
    (hne_sv_p : senderVar ≠ paramName)
    (hne_ov_p : ownerVar ≠ paramName)
    (hne_ov_sv : ownerVar ≠ senderVar)
    (hne_tv_p : targetVar ≠ paramName)
    (hne_tv_sv : targetVar ≠ senderVar)
    (hne_tv_ov : targetVar ≠ ownerVar) :
    (compileStmts fields
      (morphoSetFeeRecipientOwnerAuthStmts
        ownerField targetField senderVar ownerVar targetVar paramName msg1 msg2)).run
      (CompileState.mk 1
        [(paramName, { id := 0, ty := Ty.address })]
        #[{ id := 0, ty := Ty.address }]
        #[] #[]) =
      Except.ok ((),
        morphoSetFeeRecipientOwnerAuthExpectedState
          ownerSlot targetSlot senderVar ownerVar targetVar paramName msg1 msg2) := by
  have h1 : (senderVar == paramName) = false := beq_false_of_ne hne_sv_p
  have h2 : (ownerVar == paramName) = false := beq_false_of_ne hne_ov_p
  have h3 : (ownerVar == senderVar) = false := beq_false_of_ne hne_ov_sv
  have h4 : (targetVar == paramName) = false := beq_false_of_ne hne_tv_p
  have h5 : (targetVar == senderVar) = false := beq_false_of_ne hne_tv_sv
  have h6 : (targetVar == ownerVar) = false := beq_false_of_ne hne_tv_ov
  have hsrOwner : compileStorageRead fields ownerField =
      Except.ok ⟨Ty.address, TExpr.getStorageAddr ownerSlot⟩ := by
    simp only [compileStorageRead, hOwner, fieldTypeToTy]; rfl
  have hsrTarget : compileStorageRead fields targetField =
      Except.ok ⟨Ty.address, TExpr.getStorageAddr targetSlot⟩ := by
    simp only [compileStorageRead, hTarget, fieldTypeToTy]; rfl
  simp [morphoSetFeeRecipientOwnerAuthStmts, morphoSetFeeRecipientOwnerAuthExpectedState,
    compileStmts, compileStmt, compileExpr, hsrOwner, hsrTarget, hTarget, fieldTypeToTy,
    emitSSABind, freshVar, bindVar, pushLocal, lookupVar, asBool,
    liftExcept, emit, List.find?, h1, h2, h3, h4, monadLift]; rfl

/-- Compilation shape for an owner-auth mint pattern:
`letVar senderVar caller ; letVar ownerVar (storage ownerField) ;
 require (eq (localVar senderVar) (localVar ownerVar)) msg ;
 letVar balanceVar (mapping mappingField (param toParam)) ;
 letVar supplyVar (storage supplyField) ;
 setMapping mappingField (param toParam)
   (add (localVar balanceVar) (param amountParam)) ;
 setStorage supplyField
   (add (localVar supplyVar) (param amountParam)) ; stop`. -/
theorem compileStmts_letCallerLetStorageAddrReqEqLetMappingLetStorageSetMappingAddParamSetStorageAddParamStop_run
    (fields : List Field)
    (ownerField mappingField supplyField senderVar ownerVar balanceVar supplyVar toParam amountParam
      msg : String)
    (ownerSlot mappingSlot supplySlot : Nat)
    (hOwner : findFieldWithResolvedSlot fields ownerField =
      some ({ name := ownerField, ty := FieldType.address }, ownerSlot))
    (hMapping : findFieldSlot fields mappingField = some mappingSlot)
    (hSupply : findFieldWithResolvedSlot fields supplyField =
      some ({ name := supplyField, ty := FieldType.uint256 }, supplySlot))
    (hne_ap_tp : amountParam ≠ toParam)
    (hne_sv_tp : senderVar ≠ toParam)
    (hne_sv_ap : senderVar ≠ amountParam)
    (hne_ov_tp : ownerVar ≠ toParam)
    (hne_ov_ap : ownerVar ≠ amountParam)
    (hne_ov_sv : ownerVar ≠ senderVar)
    (hne_bv_tp : balanceVar ≠ toParam)
    (hne_bv_ap : balanceVar ≠ amountParam)
    (hne_sp_tp : supplyVar ≠ toParam)
    (hne_sp_ap : supplyVar ≠ amountParam)
    (hne_sp_bv : supplyVar ≠ balanceVar) :
    (compileStmts fields
      [ Stmt.letVar senderVar Expr.caller
      , Stmt.letVar ownerVar (Expr.storage ownerField)
      , Stmt.require (Expr.eq (Expr.localVar senderVar) (Expr.localVar ownerVar)) msg
      , Stmt.letVar balanceVar (Expr.mapping mappingField (Expr.param toParam))
      , Stmt.letVar supplyVar (Expr.storage supplyField)
      , Stmt.setMapping mappingField (Expr.param toParam)
          (Expr.add (Expr.localVar balanceVar) (Expr.param amountParam))
      , Stmt.setStorage supplyField
          (Expr.add (Expr.localVar supplyVar) (Expr.param amountParam))
      , Stmt.stop
      ]).run
      (CompileState.mk 2
        [(amountParam, { id := 1, ty := Ty.uint256 }),
         (toParam, { id := 0, ty := Ty.address })]
        #[{ id := 0, ty := Ty.address }, { id := 1, ty := Ty.uint256 }]
        #[] #[]) =
      Except.ok ((),
        { nextId := 6
          vars := [(supplyVar, { id := 5, ty := Ty.uint256 }),
                   (balanceVar, { id := 4, ty := Ty.uint256 }),
                   (ownerVar, { id := 3, ty := Ty.address }),
                   (senderVar, { id := 2, ty := Ty.address }),
                   (amountParam, { id := 1, ty := Ty.uint256 }),
                   (toParam, { id := 0, ty := Ty.address })]
          params := #[{ id := 0, ty := Ty.address }, { id := 1, ty := Ty.uint256 }]
          locals := #[{ id := 2, ty := Ty.address }, { id := 3, ty := Ty.address },
                      { id := 4, ty := Ty.uint256 }, { id := 5, ty := Ty.uint256 }]
          body := #[
            TStmt.let_ { id := 2, ty := Ty.address } TExpr.sender,
            TStmt.let_ { id := 3, ty := Ty.address } (TExpr.getStorageAddr ownerSlot),
            TStmt.if_ (TExpr.eq
                (TExpr.var { id := 2, ty := Ty.address })
                (TExpr.var { id := 3, ty := Ty.address }))
              [] [TStmt.revert msg],
            TStmt.let_ { id := 4, ty := Ty.uint256 }
              (TExpr.getMapping mappingSlot (TExpr.var { id := 0, ty := Ty.address })),
            TStmt.let_ { id := 5, ty := Ty.uint256 } (TExpr.getStorage supplySlot),
            TStmt.setMapping mappingSlot
              (TExpr.var { id := 0, ty := Ty.address })
              (TExpr.add
                (TExpr.var { id := 4, ty := Ty.uint256 })
                (TExpr.var { id := 1, ty := Ty.uint256 })),
            TStmt.setStorage supplySlot
              (TExpr.add
                (TExpr.var { id := 5, ty := Ty.uint256 })
                (TExpr.var { id := 1, ty := Ty.uint256 })),
            TStmt.stop
          ] }) := by
  have h0 : (amountParam == toParam) = false := beq_false_of_ne hne_ap_tp
  have h1 : (senderVar == toParam) = false := beq_false_of_ne hne_sv_tp
  have h2 : (senderVar == amountParam) = false := beq_false_of_ne hne_sv_ap
  have h3 : (ownerVar == toParam) = false := beq_false_of_ne hne_ov_tp
  have h4 : (ownerVar == amountParam) = false := beq_false_of_ne hne_ov_ap
  have h5 : (ownerVar == senderVar) = false := beq_false_of_ne hne_ov_sv
  have h6 : (balanceVar == toParam) = false := beq_false_of_ne hne_bv_tp
  have h7 : (balanceVar == amountParam) = false := beq_false_of_ne hne_bv_ap
  have h10 : (supplyVar == toParam) = false := beq_false_of_ne hne_sp_tp
  have h11 : (supplyVar == amountParam) = false := beq_false_of_ne hne_sp_ap
  have h14 : (supplyVar == balanceVar) = false := beq_false_of_ne hne_sp_bv
  have hsrOwner : compileStorageRead fields ownerField =
      Except.ok ⟨Ty.address, TExpr.getStorageAddr ownerSlot⟩ := by
    simp only [compileStorageRead, hOwner, fieldTypeToTy]; rfl
  have hsrSupply : compileStorageRead fields supplyField =
      Except.ok ⟨Ty.uint256, TExpr.getStorage supplySlot⟩ := by
    simp only [compileStorageRead, hSupply, fieldTypeToTy]; rfl
  simp [compileStmts, compileStmt, compileExpr, hsrOwner, hsrSupply, hSupply, fieldTypeToTy,
    emitSSABind, freshVar, bindVar, pushLocal, lookupVar, asAddress, asBool, asUInt256,
    liftExcept, emit, List.find?, hMapping, h0, h1, h2, h3, h4, h5, h6, h7, h10, h11, h14]
  rfl

/-- Compilation shape for the Morpho `enableIrm` pattern:
`letVar senderVar caller ; letVar ownerVar (storage ownerField) ;
 require (eq (localVar senderVar) (localVar ownerVar)) msg1 ;
 letVar currentVar (mapping mappingField (param keyParam)) ;
 require (eq (localVar currentVar) (literal 0)) msg2 ;
 setMapping mappingField (param keyParam) (literal writeVal) ; stop`.
This pattern is used by Morpho Blue's `enableIrm` admin function. -/
theorem compileStmts_letCallerLetStorageAddrReqEqLetMappingReqEqLitSetMappingStop_run
    (fields : List Field) (ownerField mappingField senderVar ownerVar currentVar keyParam msg1 msg2 : String)
    (ownerSlot mappingSlot : Nat) (writeVal : Nat)
    (hOwner : findFieldWithResolvedSlot fields ownerField =
      some ({ name := ownerField, ty := FieldType.address }, ownerSlot))
    (hMapping : findFieldSlot fields mappingField = some mappingSlot)
    (hne_sv_kp : senderVar ≠ keyParam)
    (hne_ov_kp : ownerVar ≠ keyParam)
    (hne_ov_sv : ownerVar ≠ senderVar)
    (hne_cv_kp : currentVar ≠ keyParam) :
    (compileStmts fields
      [ Stmt.letVar senderVar Expr.caller
      , Stmt.letVar ownerVar (Expr.storage ownerField)
      , Stmt.require (Expr.eq (Expr.localVar senderVar) (Expr.localVar ownerVar)) msg1
      , Stmt.letVar currentVar (Expr.mapping mappingField (Expr.param keyParam))
      , Stmt.require (Expr.eq (Expr.localVar currentVar) (Expr.literal 0)) msg2
      , Stmt.setMapping mappingField (Expr.param keyParam) (Expr.literal writeVal)
      , Stmt.stop
      ]).run
      (CompileState.mk 1
        [(keyParam, { id := 0, ty := Ty.address })]
        #[{ id := 0, ty := Ty.address }]
        #[] #[]) =
      Except.ok ((),
        { nextId := 4
          vars := [(currentVar, { id := 3, ty := Ty.uint256 }),
                   (ownerVar, { id := 2, ty := Ty.address }),
                   (senderVar, { id := 1, ty := Ty.address }),
                   (keyParam, { id := 0, ty := Ty.address })]
          params := #[{ id := 0, ty := Ty.address }]
          locals := #[{ id := 1, ty := Ty.address }, { id := 2, ty := Ty.address },
                      { id := 3, ty := Ty.uint256 }]
          body := #[
            TStmt.let_ { id := 1, ty := Ty.address } TExpr.sender,
            TStmt.let_ { id := 2, ty := Ty.address } (TExpr.getStorageAddr ownerSlot),
            TStmt.if_ (TExpr.eq
                (TExpr.var { id := 1, ty := Ty.address })
                (TExpr.var { id := 2, ty := Ty.address }))
              [] [TStmt.revert msg1],
            TStmt.let_ { id := 3, ty := Ty.uint256 }
              (TExpr.getMapping mappingSlot (TExpr.var { id := 0, ty := Ty.address })),
            TStmt.if_ (TExpr.eq
                (TExpr.var { id := 3, ty := Ty.uint256 })
                (TExpr.uintLit 0))
              [] [TStmt.revert msg2],
            TStmt.setMapping mappingSlot
              (TExpr.var { id := 0, ty := Ty.address })
              (TExpr.uintLit writeVal),
            TStmt.stop
          ] }) := by
  have h1 : (senderVar == keyParam) = false := beq_false_of_ne hne_sv_kp
  have h2 : (ownerVar == keyParam) = false := beq_false_of_ne hne_ov_kp
  have h3 : (ownerVar == senderVar) = false := beq_false_of_ne hne_ov_sv
  have h4 : (currentVar == keyParam) = false := beq_false_of_ne hne_cv_kp
  have hsr : compileStorageRead fields ownerField =
      Except.ok ⟨Ty.address, TExpr.getStorageAddr ownerSlot⟩ := by
    simp only [compileStorageRead, hOwner, fieldTypeToTy]; rfl
  simp [compileStmts, compileStmt, compileExpr, hsr, emitSSABind, freshVar,
    bindVar, pushLocal, lookupVar, asAddress, asBool, asUInt256, liftExcept,
    hMapping, emit, List.find?, h1, h2, h3, h4]; rfl

/-- Compilation shape for the Morpho `enableLltv` pattern:
`letVar senderVar caller ; letVar ownerVar (storage ownerField) ;
 require (eq (localVar senderVar) (localVar ownerVar)) msg1 ;
 letVar currentVar (mappingUint mappingField (param keyParam)) ;
 require (eq (localVar currentVar) (literal 0)) msg2 ;
 require (lt (param keyParam) (literal bound)) msg3 ;
 setMappingUint mappingField (param keyParam) (literal writeVal) ; stop`.
This pattern is used by Morpho Blue's `enableLltv` admin function. -/
theorem compileStmts_letCallerLetStorageAddrReqEqLetMappingUintReqEqLitReqLtSetMappingUintStop_run
    (fields : List Field) (ownerField mappingField senderVar ownerVar currentVar keyParam msg1 msg2 msg3 : String)
    (ownerSlot mappingSlot : Nat) (bound writeVal : Nat)
    (hOwner : findFieldWithResolvedSlot fields ownerField =
      some ({ name := ownerField, ty := FieldType.address }, ownerSlot))
    (hMapping : findFieldSlot fields mappingField = some mappingSlot)
    (hne_sv_kp : senderVar ≠ keyParam)
    (hne_ov_kp : ownerVar ≠ keyParam)
    (hne_ov_sv : ownerVar ≠ senderVar)
    (hne_cv_kp : currentVar ≠ keyParam) :
    (compileStmts fields
      [ Stmt.letVar senderVar Expr.caller
      , Stmt.letVar ownerVar (Expr.storage ownerField)
      , Stmt.require (Expr.eq (Expr.localVar senderVar) (Expr.localVar ownerVar)) msg1
      , Stmt.letVar currentVar (Expr.mappingUint mappingField (Expr.param keyParam))
      , Stmt.require (Expr.eq (Expr.localVar currentVar) (Expr.literal 0)) msg2
      , Stmt.require (Expr.lt (Expr.param keyParam) (Expr.literal bound)) msg3
      , Stmt.setMappingUint mappingField (Expr.param keyParam) (Expr.literal writeVal)
      , Stmt.stop
      ]).run
      (CompileState.mk 1
        [(keyParam, { id := 0, ty := Ty.uint256 })]
        #[{ id := 0, ty := Ty.uint256 }]
        #[] #[]) =
      Except.ok ((),
        { nextId := 4
          vars := [(currentVar, { id := 3, ty := Ty.uint256 }),
                   (ownerVar, { id := 2, ty := Ty.address }),
                   (senderVar, { id := 1, ty := Ty.address }),
                   (keyParam, { id := 0, ty := Ty.uint256 })]
          params := #[{ id := 0, ty := Ty.uint256 }]
          locals := #[{ id := 1, ty := Ty.address }, { id := 2, ty := Ty.address },
                      { id := 3, ty := Ty.uint256 }]
          body := #[
            TStmt.let_ { id := 1, ty := Ty.address } TExpr.sender,
            TStmt.let_ { id := 2, ty := Ty.address } (TExpr.getStorageAddr ownerSlot),
            TStmt.if_ (TExpr.eq
                (TExpr.var { id := 1, ty := Ty.address })
                (TExpr.var { id := 2, ty := Ty.address }))
              [] [TStmt.revert msg1],
            TStmt.let_ { id := 3, ty := Ty.uint256 }
              (TExpr.getMappingUint mappingSlot (TExpr.var { id := 0, ty := Ty.uint256 })),
            TStmt.if_ (TExpr.eq
                (TExpr.var { id := 3, ty := Ty.uint256 })
                (TExpr.uintLit 0))
              [] [TStmt.revert msg2],
            TStmt.if_ (TExpr.lt
                (TExpr.var { id := 0, ty := Ty.uint256 })
                (TExpr.uintLit bound))
              [] [TStmt.revert msg3],
            TStmt.setMappingUint mappingSlot
              (TExpr.var { id := 0, ty := Ty.uint256 })
              (TExpr.uintLit writeVal),
            TStmt.stop
          ] }) := by
  have h1 : (senderVar == keyParam) = false := beq_false_of_ne hne_sv_kp
  have h2 : (ownerVar == keyParam) = false := beq_false_of_ne hne_ov_kp
  have h3 : (ownerVar == senderVar) = false := beq_false_of_ne hne_ov_sv
  have h4 : (currentVar == keyParam) = false := beq_false_of_ne hne_cv_kp
  have hsr : compileStorageRead fields ownerField =
      Except.ok ⟨Ty.address, TExpr.getStorageAddr ownerSlot⟩ := by
    simp only [compileStorageRead, hOwner, fieldTypeToTy]; rfl
  simp [compileStmts, compileStmt, compileExpr, hsr, emitSSABind, freshVar,
    bindVar, pushLocal, lookupVar, asBool, asUInt256, liftExcept, hMapping,
    emit, List.find?, h1, h2, h3, h4]; rfl

/-- Compilation shape for the Morpho `setAuthorization` pattern:
`letVar senderVar caller ;
 letVar currentVar (mapping2 mappingField (localVar senderVar) (param authParam)) ;
 ite (param boolParam)
   [require (eq (localVar currentVar) (literal 0)) msg1,
    setMapping2 mappingField (localVar senderVar) (param authParam) (literal 1)]
   [require (logicalNot (eq (localVar currentVar) (literal 0))) msg2,
    setMapping2 mappingField (localVar senderVar) (param authParam) (literal 0)] ;
 stop`.
This pattern is used by Morpho Blue's `setAuthorization` admin function. -/
theorem compileStmts_letCallerLetMapping2IteParamReqSetMapping2Stop_run
    (fields : List Field) (mappingField senderVar currentVar authParam boolParam msg1 msg2 : String)
    (mappingSlot : Nat)
    (hMapping : findFieldSlot fields mappingField = some mappingSlot)
    (hne_sv_bp : senderVar ≠ boolParam)
    (hne_sv_ap : senderVar ≠ authParam)
    (hne_cv_bp : currentVar ≠ boolParam)
    (hne_cv_ap : currentVar ≠ authParam)
    (hne_cv_sv : currentVar ≠ senderVar)
    (hne_bp_ap : boolParam ≠ authParam) :
    (compileStmts fields
      [ Stmt.letVar senderVar Expr.caller
      , Stmt.letVar currentVar
          (Expr.mapping2 mappingField (Expr.localVar senderVar) (Expr.param authParam))
      , Stmt.ite (Expr.param boolParam)
          [ Stmt.require (Expr.eq (Expr.localVar currentVar) (Expr.literal 0)) msg1
          , Stmt.setMapping2 mappingField
              (Expr.localVar senderVar) (Expr.param authParam) (Expr.literal 1) ]
          [ Stmt.require (Expr.logicalNot
              (Expr.eq (Expr.localVar currentVar) (Expr.literal 0))) msg2
          , Stmt.setMapping2 mappingField
              (Expr.localVar senderVar) (Expr.param authParam) (Expr.literal 0) ]
      , Stmt.stop
      ]).run
      (CompileState.mk 2
        [(boolParam, { id := 1, ty := Ty.bool }),
         (authParam, { id := 0, ty := Ty.address })]
        #[{ id := 0, ty := Ty.address }, { id := 1, ty := Ty.bool }]
        #[] #[]) =
      Except.ok ((),
        { nextId := 4
          vars := [(currentVar, { id := 3, ty := Ty.uint256 }),
                   (senderVar, { id := 2, ty := Ty.address }),
                   (boolParam, { id := 1, ty := Ty.bool }),
                   (authParam, { id := 0, ty := Ty.address })]
          params := #[{ id := 0, ty := Ty.address }, { id := 1, ty := Ty.bool }]
          locals := #[{ id := 2, ty := Ty.address }, { id := 3, ty := Ty.uint256 }]
          body := #[
            TStmt.let_ { id := 2, ty := Ty.address } TExpr.sender,
            TStmt.let_ { id := 3, ty := Ty.uint256 }
              (TExpr.getMapping2 mappingSlot
                (TExpr.var { id := 2, ty := Ty.address })
                (TExpr.var { id := 0, ty := Ty.address })),
            TStmt.if_
              (TExpr.var { id := 1, ty := Ty.bool })
              [ TStmt.if_ (TExpr.eq
                    (TExpr.var { id := 3, ty := Ty.uint256 })
                    (TExpr.uintLit 0))
                  [] [TStmt.revert msg1],
                TStmt.setMapping2 mappingSlot
                  (TExpr.var { id := 2, ty := Ty.address })
                  (TExpr.var { id := 0, ty := Ty.address })
                  (TExpr.uintLit 1) ]
              [ TStmt.if_ (TExpr.not (TExpr.eq
                    (TExpr.var { id := 3, ty := Ty.uint256 })
                    (TExpr.uintLit 0)))
                  [] [TStmt.revert msg2],
                TStmt.setMapping2 mappingSlot
                  (TExpr.var { id := 2, ty := Ty.address })
                  (TExpr.var { id := 0, ty := Ty.address })
                  (TExpr.uintLit 0) ]
          , TStmt.stop
          ] }) := by
  have h1 : (senderVar == boolParam) = false := beq_false_of_ne hne_sv_bp
  have h2 : (senderVar == authParam) = false := beq_false_of_ne hne_sv_ap
  have h3 : (currentVar == boolParam) = false := beq_false_of_ne hne_cv_bp
  have h4 : (currentVar == authParam) = false := beq_false_of_ne hne_cv_ap
  have h5 : (currentVar == senderVar) = false := beq_false_of_ne hne_cv_sv
  have h6 : (boolParam == authParam) = false := beq_false_of_ne hne_bp_ap
  simp [compileStmts, compileStmt, compileBranch, compileExpr, emitSSABind, freshVar,
    bindVar, pushLocal, lookupVar, asAddress, asBool, asUInt256, liftExcept,
    hMapping, emit, List.find?, h1, h2, h3, h4, h5, h6]; rfl

end Verity.Core.Free
