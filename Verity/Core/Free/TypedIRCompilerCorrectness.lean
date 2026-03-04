import Verity.Core.Free.TypedIRCompiler

namespace Verity.Core.Free
open Compiler.CompilationModel

/-- Shared simplification wrappers for repeated typed-IR evaluator unfolding patterns. -/
syntax "simp_tir_eval" : tactic

macro_rules
  | `(tactic| simp_tir_eval) =>
      `(tactic| simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr])

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

/-- Direct source semantics for the storage-read + add + setStorage + stop pattern:
`letVar tmp (storage field); setStorage field (add (localVar tmp) (literal m)); stop`
reads storage slot, adds `m`, writes back. -/
def execSourceLetStorageSetStorageAddLocalStop
    (init : TExecState) (slot : Nat) (m : Nat) : TExecResult :=
  .ok { init with
    world := execSourceSetStorageLiteral init.world slot
      ((init.world.storage slot : Verity.Core.Uint256).add (m : Verity.Core.Uint256))
    vars := TVars.set init.vars { id := 0, ty := Ty.uint256 }
      (init.world.storage slot) }

/-- Compile + execute the storage-read + add + setStorage + stop pattern. -/
def execCompiledLetStorageSetStorageAddLocalStop
    (fields : List Field) (fieldName tmp : String)
    (init : TExecState) (m : Nat) : TExecResult :=
  match (compileStmts fields
      [ Stmt.letVar tmp (Expr.storage fieldName)
      , Stmt.setStorage fieldName (Expr.add (Expr.localVar tmp) (Expr.literal m))
      , Stmt.stop
      ]).run {} with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Direct source semantics for the storage-read + sub + setStorage + stop pattern:
`letVar tmp (storage field); setStorage field (sub (localVar tmp) (literal m)); stop`
reads storage slot, subtracts `m`, writes back. -/
def execSourceLetStorageSetStorageSubLocalStop
    (init : TExecState) (slot : Nat) (m : Nat) : TExecResult :=
  .ok { init with
    world := execSourceSetStorageLiteral init.world slot
      ((init.world.storage slot : Verity.Core.Uint256).sub (m : Verity.Core.Uint256))
    vars := TVars.set init.vars { id := 0, ty := Ty.uint256 }
      (init.world.storage slot) }

/-- Compile + execute the storage-read + sub + setStorage + stop pattern. -/
def execCompiledLetStorageSetStorageSubLocalStop
    (fields : List Field) (fieldName tmp : String)
    (init : TExecState) (m : Nat) : TExecResult :=
  match (compileStmts fields
      [ Stmt.letVar tmp (Expr.storage fieldName)
      , Stmt.setStorage fieldName (Expr.sub (Expr.localVar tmp) (Expr.literal m))
      , Stmt.stop
      ]).run {} with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Direct source semantics for the storage-read + return pattern:
`letVar tmp (storage field); return (localVar tmp)`
reads storage slot and halts. -/
def execSourceLetStorageReturnLocal
    (init : TExecState) (slot : Nat) : TExecResult :=
  .ok { init with
    vars := TVars.set init.vars { id := 0, ty := Ty.uint256 }
      (init.world.storage slot) }

/-- Compile + execute the storage-read + return pattern. -/
def execCompiledLetStorageReturnLocal
    (fields : List Field) (fieldName tmp : String)
    (init : TExecState) : TExecResult :=
  match (compileStmts fields
      [ Stmt.letVar tmp (Expr.storage fieldName)
      , Stmt.return (Expr.localVar tmp)
      ]).run {} with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Direct source semantics for the `return (storage field)` pattern (uint256):
reads storage slot and halts. -/
def execSourceReturnStorage
    (init : TExecState) (_slot : Nat) : TExecResult :=
  .ok init

/-- Compile + execute the `return (storage field)` pattern (uint256). -/
def execCompiledReturnStorage
    (fields : List Field) (fieldName : String)
    (init : TExecState) : TExecResult :=
  match (compileStmts fields [Stmt.return (Expr.storage fieldName)]).run {} with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Direct source semantics for the `return (storage field)` pattern (address):
reads address storage slot and halts. -/
def execSourceReturnStorageAddr
    (init : TExecState) (_slot : Nat) : TExecResult :=
  .ok init

/-- Compile + execute the `return (storage field)` pattern (address). -/
def execCompiledReturnStorageAddr
    (fields : List Field) (fieldName : String)
    (init : TExecState) : TExecResult :=
  match (compileStmts fields [Stmt.return (Expr.storage fieldName)]).run {} with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Direct source semantics for the supported mapping-return subset:
`return (mapping fieldName caller)` halts without mutating state. -/
def execSourceReturnMappingCaller
    (init : TExecState) (_slot : Nat) : TExecResult :=
  .ok init

/-- Compile + execute the `return (mapping fieldName caller)` pattern. -/
def execCompiledReturnMappingCaller
    (fields : List Field) (fieldName : String)
    (init : TExecState) : TExecResult :=
  match (compileStmts fields [Stmt.return (Expr.mapping fieldName Expr.caller)]).run {} with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Source semantics for the address storage-read + return pattern:
`letVar tmp (storage field); return (localVar tmp)` where field is address. -/
def execSourceLetStorageAddrReturnLocal
    (init : TExecState) (slot : Nat) : TExecResult :=
  .ok { init with
    vars := TVars.set init.vars { id := 0, ty := Ty.address }
      (init.world.storageAddr slot) }

/-- Compile + execute the address storage-read + return pattern. -/
def execCompiledLetStorageAddrReturnLocal
    (fields : List Field) (fieldName tmp : String)
    (init : TExecState) : TExecResult :=
  match (compileStmts fields
      [ Stmt.letVar tmp (Expr.storage fieldName)
      , Stmt.return (Expr.localVar tmp)
      ]).run {} with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Source semantics for the mapping(param) read + return pattern:
`letVar tmp (mapping field (param p)); return (localVar tmp)`.
Reads mapping at slot keyed by the param's address value. -/
def execSourceLetMappingParamReturnLocal
    (init : TExecState) (slot : Nat) : TExecResult :=
  .ok { init with
    vars := TVars.set init.vars { id := 1, ty := Ty.uint256 }
      (init.world.storageMap slot (init.vars.address 0)) }

/-- Compile + execute the mapping(param) read + return pattern,
from a pre-populated 1-param CompileState. -/
def execCompiledLetMappingParamReturnLocal
    (fields : List Field) (fieldName paramName tmp : String)
    (init : TExecState) : TExecResult :=
  match (compileStmts fields
      [ Stmt.letVar tmp (Expr.mapping fieldName (Expr.param paramName))
      , Stmt.return (Expr.localVar tmp)
      ]).run
      (CompileState.mk 1
        [(paramName, { id := 0, ty := Ty.address })]
        #[{ id := 0, ty := Ty.address }]
        #[] #[]) with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Source semantics for the mapping2(param1, param2) read + return pattern:
`letVar tmp (mapping2 field (param p1) (param p2)); return (localVar tmp)`. -/
def execSourceLetMapping2ParamsReturnLocal
    (init : TExecState) (slot : Nat) : TExecResult :=
  .ok { init with
    vars := TVars.set init.vars { id := 2, ty := Ty.uint256 }
      (init.world.storageMap2 slot (init.vars.address 0) (init.vars.address 1)) }

/-- Compile + execute the mapping2(param1, param2) read + return pattern,
from a pre-populated 2-address-param CompileState. -/
def execCompiledLetMapping2ParamsReturnLocal
    (fields : List Field) (fieldName p1 p2 tmp : String)
    (init : TExecState) : TExecResult :=
  match (compileStmts fields
      [ Stmt.letVar tmp (Expr.mapping2 fieldName (Expr.param p1) (Expr.param p2))
      , Stmt.return (Expr.localVar tmp)
      ]).run
      (CompileState.mk 2
        [(p2, { id := 1, ty := Ty.address }),
         (p1, { id := 0, ty := Ty.address })]
        #[{ id := 0, ty := Ty.address }, { id := 1, ty := Ty.address }]
        #[] #[]) with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Source semantics for the approve pattern:
`letVar sender caller; setMapping2 field (localVar sender) (param spender) (param amount); stop`.
Sets the double mapping at slot: mapping2[sender][spender] = amount. -/
def execSourceLetCallerSetMapping2Stop
    (init : TExecState) (slot : Nat) : TExecResult :=
  .ok { init with
    vars := TVars.set init.vars { id := 2, ty := Ty.address } init.env.sender,
    world := { init.world with
      storageMap2 := fun i a1 a2 =>
        if i == slot && a1 == init.env.sender && a2 == init.vars.address 0
        then init.vars.uint256 1
        else init.world.storageMap2 i a1 a2 } }

/-- Compile + execute the approve pattern from a pre-populated 2-param state
(spender: address, amount: uint256). -/
def execCompiledLetCallerSetMapping2Stop
    (fields : List Field) (fieldName senderVar p1 p2 : String)
    (init : TExecState) : TExecResult :=
  match (compileStmts fields
      [ Stmt.letVar senderVar Expr.caller
      , Stmt.setMapping2 fieldName (Expr.localVar senderVar) (Expr.param p1) (Expr.param p2)
      , Stmt.stop
      ]).run
      (CompileState.mk 2
        [(p2, { id := 1, ty := Ty.uint256 }),
         (p1, { id := 0, ty := Ty.address })]
        #[{ id := 0, ty := Ty.address }, { id := 1, ty := Ty.uint256 }]
        #[] #[]) with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Source semantics for `letVar tmp (mappingUint field (param p)); return (localVar tmp)`.
Reads a Uint256-keyed mapping at slot using param 0 (Uint256) as key. -/
def execSourceLetMappingUintParamReturnLocal
    (init : TExecState) (slot : Nat) : TExecResult :=
  .ok { init with
    vars := TVars.set init.vars { id := 1, ty := Ty.uint256 }
      (init.world.storageMapUint slot (init.vars.uint256 0)) }

/-- Compile + execute the mappingUint(param) read + return pattern,
from a pre-populated 1-Uint256-param CompileState. -/
def execCompiledLetMappingUintParamReturnLocal
    (fields : List Field) (fieldName paramName tmp : String)
    (init : TExecState) : TExecResult :=
  match (compileStmts fields
      [ Stmt.letVar tmp (Expr.mappingUint fieldName (Expr.param paramName))
      , Stmt.return (Expr.localVar tmp)
      ]).run
      (CompileState.mk 1
        [(paramName, { id := 0, ty := Ty.uint256 })]
        #[{ id := 0, ty := Ty.uint256 }]
        #[] #[]) with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Source semantics for `setMappingUint field (param p1) (param p2); stop`.
Sets a Uint256-keyed mapping at slot: mapping[p1] = p2. -/
def execSourceSetMappingUintParamsStop
    (init : TExecState) (slot : Nat) : TExecResult :=
  .ok { init with world := { init.world with
    storageMapUint := fun i key' =>
      if i == slot && key' == init.vars.uint256 0
      then init.vars.uint256 1
      else init.world.storageMapUint i key' } }

/-- Compile + execute the setMappingUint(param1, param2) + stop pattern,
from a pre-populated 2-Uint256-param CompileState. -/
def execCompiledSetMappingUintParamsStop
    (fields : List Field) (fieldName p1 p2 : String)
    (init : TExecState) : TExecResult :=
  match (compileStmts fields
      [ Stmt.setMappingUint fieldName (Expr.param p1) (Expr.param p2)
      , Stmt.stop
      ]).run
      (CompileState.mk 2
        [(p2, { id := 1, ty := Ty.uint256 }),
         (p1, { id := 0, ty := Ty.uint256 })]
        #[{ id := 0, ty := Ty.uint256 }, { id := 1, ty := Ty.uint256 }]
        #[] #[]) with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Source semantics for `require (eq caller (storage ownerField)) msg ;
setStorage countField (add (storage countField) (literal n)) ; stop`. -/
def execSourceRequireCallerEqStorageAddrSetStorageAddStop
    (init : TExecState) (ownerSlot countSlot : Nat) (n : Nat)
    (msg : String) : TExecResult :=
  if decide (init.env.sender = init.world.storageAddr ownerSlot) then
    .ok { init with world := { init.world with
      storage := fun i => if i == countSlot then
        Verity.Core.Uint256.add (init.world.storage countSlot) n else init.world.storage i } }
  else .revert msg

/-- Compiled semantics for `require (eq caller (storage ownerField)) msg ;
setStorage countField (add (storage countField) (literal n)) ; stop`. -/
def execCompiledRequireCallerEqStorageAddrSetStorageAddStop
    (fields : List Field) (ownerField countField : String)
    (init : TExecState) (n : Nat) (msg : String) : TExecResult :=
  match (compileStmts fields
      [ Stmt.require (Expr.eq Expr.caller (Expr.storage ownerField)) msg
      , Stmt.setStorage countField (Expr.add (Expr.storage countField) (Expr.literal n))
      , Stmt.stop ]).run {} with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Source semantics for `require (eq caller (storage ownerField)) msg ;
setStorage countField (sub (storage countField) (literal n)) ; stop`. -/
def execSourceRequireCallerEqStorageAddrSetStorageSubStop
    (init : TExecState) (ownerSlot countSlot : Nat) (n : Nat)
    (msg : String) : TExecResult :=
  if decide (init.env.sender = init.world.storageAddr ownerSlot) then
    .ok { init with world := { init.world with
      storage := fun i => if i == countSlot then
        Verity.Core.Uint256.sub (init.world.storage countSlot) n else init.world.storage i } }
  else .revert msg

/-- Compiled semantics for `require (eq caller (storage ownerField)) msg ;
setStorage countField (sub (storage countField) (literal n)) ; stop`. -/
def execCompiledRequireCallerEqStorageAddrSetStorageSubStop
    (fields : List Field) (ownerField countField : String)
    (init : TExecState) (n : Nat) (msg : String) : TExecResult :=
  match (compileStmts fields
      [ Stmt.require (Expr.eq Expr.caller (Expr.storage ownerField)) msg
      , Stmt.setStorage countField (Expr.sub (Expr.storage countField) (Expr.literal n))
      , Stmt.stop ]).run {} with
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

/-- Direct source semantics for a broader supported nested heterogeneous branch
subset:
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [return (literal thenVal)]
          [return (literal elseVal)]]
     [setStorage fieldName (literal outerElseWriteVal);
      return (literal outerElseRetVal)]`
halts via nested returns on outer-guard success; otherwise writes storage then
returns. -/
def execSourceIteEqThenIteEqReturnLiteralsThenSetStorageLiteralThenReturnLiteral
    (init : TExecState) (slot : Nat)
    (n m p q thenVal elseVal outerElseWriteVal outerElseRetVal : Nat) : TExecResult :=
  if (n : Verity.Core.Uint256) == (m : Verity.Core.Uint256) then
    execSourceIteEqReturnLiterals init p q thenVal elseVal
  else
    execSourceReturnLiteral
      { init with world := execSourceSetStorageLiteral init.world slot outerElseWriteVal }
      outerElseRetVal

/-- Compile + execute a broader supported nested heterogeneous branch subset
through typed IR. -/
def execCompiledIteEqThenIteEqReturnLiteralsThenSetStorageLiteralThenReturnLiteral
    (fields : List Field) (fieldName : String) (init : TExecState)
    (n m p q thenVal elseVal outerElseWriteVal outerElseRetVal : Nat) : TExecResult :=
  match (compileStmts fields
      [Stmt.ite
        (Expr.eq (Expr.literal n) (Expr.literal m))
        [Stmt.ite
          (Expr.eq (Expr.literal p) (Expr.literal q))
          [Stmt.return (Expr.literal thenVal)]
          [Stmt.return (Expr.literal elseVal)]]
        [Stmt.setStorage fieldName (Expr.literal outerElseWriteVal),
         Stmt.return (Expr.literal outerElseRetVal)] ]).run {} with
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

/-- Direct source semantics for a broader supported nested heterogeneous branch
subset:
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [setStorage fieldName (literal thenVal)]
          [return (literal elseVal)]]
     [return (literal outerElseVal)]`
evaluates the inner heterogeneous branch on outer-guard success and returns on
outer-guard failure. -/
def execSourceIteEqThenIteEqSetStorageThenReturnLiteralThenReturnLiteral
    (init : TExecState) (slot : Nat)
    (n m p q thenVal elseVal outerElseVal : Nat) : TExecResult :=
  if (n : Verity.Core.Uint256) == (m : Verity.Core.Uint256) then
    execSourceIteEqSetStorageThenReturnLiteral init slot p q thenVal elseVal
  else
    execSourceReturnLiteral init outerElseVal

/-- Compile + execute a broader supported nested heterogeneous branch subset
through typed IR. -/
def execCompiledIteEqThenIteEqSetStorageThenReturnLiteralThenReturnLiteral
    (fields : List Field) (fieldName : String) (init : TExecState)
    (n m p q thenVal elseVal outerElseVal : Nat) : TExecResult :=
  match (compileStmts fields
      [Stmt.ite
        (Expr.eq (Expr.literal n) (Expr.literal m))
        [Stmt.ite
          (Expr.eq (Expr.literal p) (Expr.literal q))
          [Stmt.setStorage fieldName (Expr.literal thenVal)]
          [Stmt.return (Expr.literal elseVal)]]
        [Stmt.return (Expr.literal outerElseVal)] ]).run {} with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Direct source semantics for a broader supported nested heterogeneous branch
subset:
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [setStorage fieldName (literal thenVal)]
          [return (literal elseVal)]]
     [setStorage fieldName (literal outerElseVal)]`
evaluates the inner heterogeneous branch on outer-guard success and writes
storage on outer-guard failure. -/
def execSourceIteEqThenIteEqSetStorageThenReturnLiteralThenSetStorageLiteral
    (init : TExecState) (slot : Nat)
    (n m p q thenVal elseVal outerElseVal : Nat) : TExecResult :=
  if (n : Verity.Core.Uint256) == (m : Verity.Core.Uint256) then
    execSourceIteEqSetStorageThenReturnLiteral init slot p q thenVal elseVal
  else
    .ok { init with world := execSourceSetStorageLiteral init.world slot outerElseVal }

/-- Compile + execute a broader supported nested heterogeneous branch subset
through typed IR. -/
def execCompiledIteEqThenIteEqSetStorageThenReturnLiteralThenSetStorageLiteral
    (fields : List Field) (fieldName : String) (init : TExecState)
    (n m p q thenVal elseVal outerElseVal : Nat) : TExecResult :=
  match (compileStmts fields
      [Stmt.ite
        (Expr.eq (Expr.literal n) (Expr.literal m))
        [Stmt.ite
          (Expr.eq (Expr.literal p) (Expr.literal q))
          [Stmt.setStorage fieldName (Expr.literal thenVal)]
          [Stmt.return (Expr.literal elseVal)]]
        [Stmt.setStorage fieldName (Expr.literal outerElseVal)] ]).run {} with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Direct source semantics for a broader supported nested heterogeneous branch
subset:
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [return (literal thenVal)]
          [setStorage fieldName (literal elseVal)]]
     [return (literal outerElseVal)]`
evaluates the inner heterogeneous branch on outer-guard success and returns on
outer-guard failure. -/
def execSourceIteEqThenIteEqReturnThenSetStorageLiteralThenReturnLiteral
    (init : TExecState) (slot : Nat)
    (n m p q thenVal elseVal outerElseVal : Nat) : TExecResult :=
  if (n : Verity.Core.Uint256) == (m : Verity.Core.Uint256) then
    execSourceIteEqReturnThenSetStorageLiteral init slot p q thenVal elseVal
  else
    execSourceReturnLiteral init outerElseVal

/-- Compile + execute a broader supported nested heterogeneous branch subset
through typed IR. -/
def execCompiledIteEqThenIteEqReturnThenSetStorageLiteralThenReturnLiteral
    (fields : List Field) (fieldName : String) (init : TExecState)
    (n m p q thenVal elseVal outerElseVal : Nat) : TExecResult :=
  match (compileStmts fields
      [Stmt.ite
        (Expr.eq (Expr.literal n) (Expr.literal m))
        [Stmt.ite
          (Expr.eq (Expr.literal p) (Expr.literal q))
          [Stmt.return (Expr.literal thenVal)]
          [Stmt.setStorage fieldName (Expr.literal elseVal)]]
        [Stmt.return (Expr.literal outerElseVal)] ]).run {} with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Direct source semantics for a broader supported nested heterogeneous branch
subset:
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [return (literal thenVal)]
          [setStorage fieldName (literal elseVal)]]
     [setStorage fieldName (literal outerElseVal)]`
evaluates the inner heterogeneous branch on outer-guard success and writes
storage on outer-guard failure. -/
def execSourceIteEqThenIteEqReturnThenSetStorageLiteralThenSetStorageLiteral
    (init : TExecState) (slot : Nat)
    (n m p q thenVal elseVal outerElseVal : Nat) : TExecResult :=
  if (n : Verity.Core.Uint256) == (m : Verity.Core.Uint256) then
    execSourceIteEqReturnThenSetStorageLiteral init slot p q thenVal elseVal
  else
    .ok { init with world := execSourceSetStorageLiteral init.world slot outerElseVal }

/-- Compile + execute a broader supported nested heterogeneous branch subset
through typed IR. -/
def execCompiledIteEqThenIteEqReturnThenSetStorageLiteralThenSetStorageLiteral
    (fields : List Field) (fieldName : String) (init : TExecState)
    (n m p q thenVal elseVal outerElseVal : Nat) : TExecResult :=
  match (compileStmts fields
      [Stmt.ite
        (Expr.eq (Expr.literal n) (Expr.literal m))
        [Stmt.ite
          (Expr.eq (Expr.literal p) (Expr.literal q))
          [Stmt.return (Expr.literal thenVal)]
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
  simp_tir_eval

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
  simp_tir_eval

/-- Semantic-preservation theorem for the storage-read + add + setStorage + stop pattern:
compiling and running
`letVar tmp (storage field); setStorage field (add (localVar tmp) (literal m)); stop`
computes the expected state. -/
theorem compile_let_storage_setStorage_add_local_stop_semantics
    (fields : List Field) (fieldName tmp : String) (slot : Nat)
    (init : TExecState) (m : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledLetStorageSetStorageAddLocalStop fields fieldName tmp init m =
      execSourceLetStorageSetStorageAddLocalStop init slot m := by
  simp [execCompiledLetStorageSetStorageAddLocalStop,
    execSourceLetStorageSetStorageAddLocalStop, execSourceSetStorageLiteral,
    compileStmts_let_storage_setStorage_add_local_stop_run, hfind,
    evalTStmts, defaultEvalFuel]
  simp_tir_eval

/-- Semantic-preservation theorem for the storage-read + sub + setStorage + stop pattern:
compiling and running
`letVar tmp (storage field); setStorage field (sub (localVar tmp) (literal m)); stop`
computes the expected state. -/
theorem compile_let_storage_setStorage_sub_local_stop_semantics
    (fields : List Field) (fieldName tmp : String) (slot : Nat)
    (init : TExecState) (m : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledLetStorageSetStorageSubLocalStop fields fieldName tmp init m =
      execSourceLetStorageSetStorageSubLocalStop init slot m := by
  simp [execCompiledLetStorageSetStorageSubLocalStop,
    execSourceLetStorageSetStorageSubLocalStop, execSourceSetStorageLiteral,
    compileStmts_let_storage_setStorage_sub_local_stop_run, hfind,
    evalTStmts, defaultEvalFuel]
  simp_tir_eval

/-- Semantic-preservation theorem for the storage-read + return pattern:
compiling and running
`letVar tmp (storage field); return (localVar tmp)`
computes the expected state. -/
theorem compile_let_storage_return_local_semantics
    (fields : List Field) (fieldName tmp : String) (slot : Nat)
    (init : TExecState)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledLetStorageReturnLocal fields fieldName tmp init =
      execSourceLetStorageReturnLocal init slot := by
  simp [execCompiledLetStorageReturnLocal, execSourceLetStorageReturnLocal,
    compileStmts_let_storage_return_local_run, hfind,
    evalTStmts, defaultEvalFuel]
  simp_tir_eval

/-- Semantic-preservation theorem for `return (storage field)` (uint256). -/
theorem compile_return_storage_semantics
    (fields : List Field) (fieldName : String) (slot : Nat)
    (init : TExecState)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledReturnStorage fields fieldName init =
      execSourceReturnStorage init slot := by
  simp [execCompiledReturnStorage, execSourceReturnStorage,
    compileStmts_single_return_storage_run, hfind,
    evalTStmts, defaultEvalFuel]
  simp [evalTStmtsFuel, evalTStmtFuel]

/-- Semantic-preservation theorem for `return (storage field)` (address). -/
theorem compile_return_storage_addr_semantics
    (fields : List Field) (fieldName : String) (slot : Nat)
    (init : TExecState)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.address }, slot)) :
    execCompiledReturnStorageAddr fields fieldName init =
      execSourceReturnStorageAddr init slot := by
  simp [execCompiledReturnStorageAddr, execSourceReturnStorageAddr,
    compileStmts_single_return_storage_addr_run, hfind,
    evalTStmts, defaultEvalFuel]
  simp [evalTStmtsFuel, evalTStmtFuel]

/-- Semantic-preservation for `return (mapping fieldName caller)`:
compiled execution matches direct source semantics (no state change). -/
theorem compile_return_mapping_caller_semantics
    (fields : List Field) (fieldName : String) (slot : Nat)
    (init : TExecState)
    (hSlot : findFieldSlot fields fieldName = some slot) :
    execCompiledReturnMappingCaller fields fieldName init =
      execSourceReturnMappingCaller init slot := by
  simp [execCompiledReturnMappingCaller, execSourceReturnMappingCaller,
    compileStmts_single_return_mapping_caller_run, hSlot,
    evalTStmts, defaultEvalFuel]
  simp [evalTStmtsFuel, evalTStmtFuel]

/-- Semantic-preservation for the address storage-read + return pattern. -/
theorem compile_let_storage_addr_return_local_semantics
    (fields : List Field) (fieldName tmp : String) (slot : Nat)
    (init : TExecState)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.address }, slot)) :
    execCompiledLetStorageAddrReturnLocal fields fieldName tmp init =
      execSourceLetStorageAddrReturnLocal init slot := by
  simp [execCompiledLetStorageAddrReturnLocal, execSourceLetStorageAddrReturnLocal,
    compileStmts_let_storage_addr_return_local_run, hfind,
    evalTStmts, defaultEvalFuel]
  simp_tir_eval

/-- Semantic-preservation for the mapping(param) read + return pattern. -/
theorem compile_let_mapping_param_return_local_semantics
    (fields : List Field) (fieldName paramName tmp : String) (slot : Nat)
    (init : TExecState)
    (hSlot : findFieldSlot fields fieldName = some slot) :
    execCompiledLetMappingParamReturnLocal fields fieldName paramName tmp init =
      execSourceLetMappingParamReturnLocal init slot := by
  simp [execCompiledLetMappingParamReturnLocal, execSourceLetMappingParamReturnLocal,
    compileStmts_let_mapping_param_return_local_run, hSlot,
    evalTStmts, defaultEvalFuel]
  simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, TVars.get]

/-- Semantic-preservation for the mapping2(param1, param2) read + return pattern. -/
theorem compile_let_mapping2_params_return_local_semantics
    (fields : List Field) (fieldName p1 p2 tmp : String) (slot : Nat)
    (init : TExecState)
    (hSlot : findFieldSlot fields fieldName = some slot)
    (hp : p1 ≠ p2) :
    execCompiledLetMapping2ParamsReturnLocal fields fieldName p1 p2 tmp init =
      execSourceLetMapping2ParamsReturnLocal init slot := by
  simp [execCompiledLetMapping2ParamsReturnLocal, execSourceLetMapping2ParamsReturnLocal,
    compileStmts_let_mapping2_params_return_local_run, hSlot, hp,
    evalTStmts, defaultEvalFuel]
  simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, TVars.get]

/-- Semantic-preservation for the approve pattern:
`letVar sender caller; setMapping2 field sender spender amount; stop`. -/
theorem compile_let_caller_setMapping2_stop_semantics
    (fields : List Field) (fieldName senderVar p1 p2 : String) (slot : Nat)
    (init : TExecState)
    (hSlot : findFieldSlot fields fieldName = some slot)
    (h1 : senderVar ≠ p2) (h2 : senderVar ≠ p1) (h3 : p2 ≠ p1)
    (h4 : p1 ≠ p2) (h5 : p1 ≠ senderVar) (h6 : p2 ≠ senderVar) :
    execCompiledLetCallerSetMapping2Stop fields fieldName senderVar p1 p2 init =
      execSourceLetCallerSetMapping2Stop init slot := by
  simp [execCompiledLetCallerSetMapping2Stop, execSourceLetCallerSetMapping2Stop,
    compileStmts_let_caller_setMapping2_stop_run, hSlot,
    h1, h2, h3, h4, h5, h6,
    evalTStmts, defaultEvalFuel]
  simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, TVars.get, TVars.set]

/-- Semantic-preservation for the mappingUint(param) read + return pattern. -/
theorem compile_let_mappingUint_param_return_local_semantics
    (fields : List Field) (fieldName paramName tmp : String) (slot : Nat)
    (init : TExecState)
    (hSlot : findFieldSlot fields fieldName = some slot) :
    execCompiledLetMappingUintParamReturnLocal fields fieldName paramName tmp init =
      execSourceLetMappingUintParamReturnLocal init slot := by
  simp [execCompiledLetMappingUintParamReturnLocal, execSourceLetMappingUintParamReturnLocal,
    compileStmts_let_mappingUint_param_return_local_run, hSlot,
    evalTStmts, defaultEvalFuel]
  simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, TVars.get]

/-- Semantic-preservation for the setMappingUint(param1, param2) + stop pattern. -/
theorem compile_setMappingUint_params_stop_semantics
    (fields : List Field) (fieldName p1 p2 : String) (slot : Nat)
    (init : TExecState)
    (hSlot : findFieldSlot fields fieldName = some slot)
    (hp : p1 ≠ p2) :
    execCompiledSetMappingUintParamsStop fields fieldName p1 p2 init =
      execSourceSetMappingUintParamsStop init slot := by
  simp [execCompiledSetMappingUintParamsStop, execSourceSetMappingUintParamsStop,
    compileStmts_setMappingUint_params_stop_run, hSlot, hp,
    evalTStmts, defaultEvalFuel]
  simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, TVars.get]

-- ============================================================================
-- Morpho Blue admin function base semantics definitions
-- ============================================================================

/-- Source semantics for the Morpho setOwner/setFeeRecipient pattern.
Params: paramName (address, id 0).
Locals: senderVar (address, id 1), ownerVar (address, id 2). -/
def execSourceLetCallerLetStorageAddrReqEqReqNeqSetStorageAddrParamStop
    (init : TExecState) (ownerSlot : Nat) (msg1 msg2 : String) : TExecResult :=
  let sender := init.env.sender
  let owner := init.world.storageAddr ownerSlot
  let param := init.vars.address 0
  if decide (sender = owner) then
    if decide (¬ (param = owner)) then
      .ok { init with
        vars := TVars.set (TVars.set init.vars
          { id := 1, ty := Ty.address } sender)
          { id := 2, ty := Ty.address } owner,
        world := { init.world with
          storageAddr := fun i => if i == ownerSlot then param else init.world.storageAddr i } }
    else .revert msg2
  else .revert msg1

/-- Compiled semantics for the Morpho setOwner/setFeeRecipient pattern.
Pre-populated CompileState: paramName (address, id 0). -/
def execCompiledLetCallerLetStorageAddrReqEqReqNeqSetStorageAddrParamStop
    (fields : List Field) (ownerField senderVar ownerVar paramName : String)
    (msg1 msg2 : String) (init : TExecState) : TExecResult :=
  match (compileStmts fields
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
        #[] #[]) with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Source semantics for the Morpho enableIrm pattern.
Params: keyParam (address, id 0).
Locals: senderVar (address, id 1), ownerVar (address, id 2), currentVar (uint256, id 3). -/
def execSourceLetCallerLetStorageAddrReqEqLetMappingReqEqLitSetMappingStop
    (init : TExecState) (ownerSlot mappingSlot : Nat) (writeVal : Nat)
    (msg1 msg2 : String) : TExecResult :=
  let sender := init.env.sender
  let owner := init.world.storageAddr ownerSlot
  let key := init.vars.address 0
  if decide (sender = owner) then
    let currentVal := init.world.storageMap mappingSlot key
    if decide ((currentVal : Verity.Core.Uint256) = (0 : Verity.Core.Uint256)) then
      .ok { init with
        vars := TVars.set (TVars.set (TVars.set init.vars
          { id := 1, ty := Ty.address } sender)
          { id := 2, ty := Ty.address } owner)
          { id := 3, ty := Ty.uint256 } currentVal,
        world := { init.world with
          storageMap := fun i a => if i == mappingSlot && a == key
            then (writeVal : Verity.Core.Uint256)
            else init.world.storageMap i a } }
    else .revert msg2
  else .revert msg1

/-- Compiled semantics for the Morpho enableIrm pattern.
Pre-populated CompileState: keyParam (address, id 0). -/
def execCompiledLetCallerLetStorageAddrReqEqLetMappingReqEqLitSetMappingStop
    (fields : List Field) (ownerField mappingField senderVar ownerVar currentVar keyParam : String)
    (writeVal : Nat) (msg1 msg2 : String) (init : TExecState) : TExecResult :=
  match (compileStmts fields
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
        #[] #[]) with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Source semantics for the Morpho enableLltv pattern.
Params: keyParam (uint256, id 0).
Locals: senderVar (address, id 1), ownerVar (address, id 2), currentVar (uint256, id 3). -/
def execSourceLetCallerLetStorageAddrReqEqLetMappingUintReqEqLitReqLtSetMappingUintStop
    (init : TExecState) (ownerSlot mappingSlot : Nat) (bound writeVal : Nat)
    (msg1 msg2 msg3 : String) : TExecResult :=
  let sender := init.env.sender
  let owner := init.world.storageAddr ownerSlot
  let key := init.vars.uint256 0
  if decide (sender = owner) then
    let currentVal := init.world.storageMapUint mappingSlot key
    if decide ((currentVal : Verity.Core.Uint256) = (0 : Verity.Core.Uint256)) then
      if decide ((key : Verity.Core.Uint256) < (bound : Verity.Core.Uint256)) then
        .ok { init with
          vars := TVars.set (TVars.set (TVars.set init.vars
            { id := 1, ty := Ty.address } sender)
            { id := 2, ty := Ty.address } owner)
            { id := 3, ty := Ty.uint256 } currentVal,
          world := { init.world with
            storageMapUint := fun i k => if i == mappingSlot && k == key
              then (writeVal : Verity.Core.Uint256)
              else init.world.storageMapUint i k } }
      else .revert msg3
    else .revert msg2
  else .revert msg1

/-- Compiled semantics for the Morpho enableLltv pattern.
Pre-populated CompileState: keyParam (uint256, id 0). -/
def execCompiledLetCallerLetStorageAddrReqEqLetMappingUintReqEqLitReqLtSetMappingUintStop
    (fields : List Field) (ownerField mappingField senderVar ownerVar currentVar keyParam : String)
    (bound writeVal : Nat) (msg1 msg2 msg3 : String) (init : TExecState) : TExecResult :=
  match (compileStmts fields
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
        #[] #[]) with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Source semantics for the Morpho setAuthorization pattern.
Params: authParam (address, id 0), boolParam (bool, id 1).
Locals: senderVar (address, id 2), currentVar (uint256, id 3). -/
def execSourceLetCallerLetMapping2IteParamReqSetMapping2Stop
    (init : TExecState) (mappingSlot : Nat) (msg1 msg2 : String) : TExecResult :=
  let sender := init.env.sender
  let authAddr := init.vars.address 0
  let currentVal := init.world.storageMap2 mappingSlot sender authAddr
  if init.vars.bool 1 then
    if decide ((currentVal : Verity.Core.Uint256) = (0 : Verity.Core.Uint256)) then
      .ok { init with
        vars := TVars.set (TVars.set init.vars
          { id := 2, ty := Ty.address } sender)
          { id := 3, ty := Ty.uint256 } currentVal,
        world := { init.world with
          storageMap2 := fun i a1 a2 => if i == mappingSlot && a1 == sender && a2 == authAddr
            then (1 : Verity.Core.Uint256)
            else init.world.storageMap2 i a1 a2 } }
    else .revert msg1
  else
    if decide (¬ ((currentVal : Verity.Core.Uint256) = (0 : Verity.Core.Uint256))) then
      .ok { init with
        vars := TVars.set (TVars.set init.vars
          { id := 2, ty := Ty.address } sender)
          { id := 3, ty := Ty.uint256 } currentVal,
        world := { init.world with
          storageMap2 := fun i a1 a2 => if i == mappingSlot && a1 == sender && a2 == authAddr
            then (0 : Verity.Core.Uint256)
            else init.world.storageMap2 i a1 a2 } }
    else .revert msg2

/-- Compiled semantics for the Morpho setAuthorization pattern.
Pre-populated CompileState: authParam (address, id 0), boolParam (bool, id 1). -/
def execCompiledLetCallerLetMapping2IteParamReqSetMapping2Stop
    (fields : List Field) (mappingField senderVar currentVar authParam boolParam : String)
    (msg1 msg2 : String) (init : TExecState) : TExecResult :=
  match (compileStmts fields
      [ Stmt.letVar senderVar Expr.caller
      , Stmt.letVar currentVar (Expr.mapping2 mappingField (Expr.localVar senderVar) (Expr.param authParam))
      , Stmt.ite (Expr.param boolParam)
          [ Stmt.require (Expr.eq (Expr.localVar currentVar) (Expr.literal 0)) msg1
          , Stmt.setMapping2 mappingField (Expr.localVar senderVar) (Expr.param authParam) (Expr.literal 1)
          ]
          [ Stmt.require (Expr.logicalNot (Expr.eq (Expr.localVar currentVar) (Expr.literal 0))) msg2
          , Stmt.setMapping2 mappingField (Expr.localVar senderVar) (Expr.param authParam) (Expr.literal 0)
          ]
      , Stmt.stop
      ]).run
      (CompileState.mk 2
        [(boolParam, { id := 1, ty := Ty.bool }),
         (authParam, { id := 0, ty := Ty.address })]
        #[{ id := 0, ty := Ty.address }, { id := 1, ty := Ty.bool }]
        #[] #[]) with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

-- ============================================================================
-- Morpho Blue admin function correctness theorems
-- ============================================================================

/-- Semantic-preservation for the Morpho setOwner/setFeeRecipient pattern. -/
theorem compile_letCaller_letStorageAddr_reqEq_reqNeq_setStorageAddr_param_stop_semantics
    (fields : List Field) (ownerField senderVar ownerVar paramName msg1 msg2 : String)
    (ownerSlot : Nat) (init : TExecState)
    (hOwner : findFieldWithResolvedSlot fields ownerField =
      some ({ name := ownerField, ty := FieldType.address }, ownerSlot))
    (hne_sv_p : senderVar ≠ paramName)
    (hne_ov_p : ownerVar ≠ paramName)
    (hne_ov_sv : ownerVar ≠ senderVar) :
    execCompiledLetCallerLetStorageAddrReqEqReqNeqSetStorageAddrParamStop
        fields ownerField senderVar ownerVar paramName msg1 msg2 init =
      execSourceLetCallerLetStorageAddrReqEqReqNeqSetStorageAddrParamStop
        init ownerSlot msg1 msg2 := by
  simp [execCompiledLetCallerLetStorageAddrReqEqReqNeqSetStorageAddrParamStop,
    execSourceLetCallerLetStorageAddrReqEqReqNeqSetStorageAddrParamStop,
    compileStmts_letCallerLetStorageAddrReqEqReqNeqSetStorageAddrParamStop_run,
    hOwner, hne_sv_p, hne_ov_p, hne_ov_sv,
    evalTStmts, defaultEvalFuel]
  by_cases hEq1 : init.env.sender = init.world.storageAddr ownerSlot
  · by_cases hEq2 : init.vars.address 0 = init.world.storageAddr ownerSlot
    · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEq1, hEq2, TVars.set, TVars.get]
    · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEq1, hEq2, TVars.set, TVars.get]
  · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEq1, TVars.set, TVars.get]

/-- Semantic-preservation for the Morpho enableIrm pattern. -/
theorem compile_letCaller_letStorageAddr_reqEq_letMapping_reqEqLit_setMapping_stop_semantics
    (fields : List Field) (ownerField mappingField senderVar ownerVar currentVar keyParam : String)
    (ownerSlot mappingSlot : Nat) (writeVal : Nat) (init : TExecState) (msg1 msg2 : String)
    (hOwner : findFieldWithResolvedSlot fields ownerField =
      some ({ name := ownerField, ty := FieldType.address }, ownerSlot))
    (hMapping : findFieldSlot fields mappingField = some mappingSlot)
    (hne_sv_kp : senderVar ≠ keyParam)
    (hne_ov_kp : ownerVar ≠ keyParam)
    (hne_ov_sv : ownerVar ≠ senderVar)
    (hne_cv_kp : currentVar ≠ keyParam) :
    execCompiledLetCallerLetStorageAddrReqEqLetMappingReqEqLitSetMappingStop
        fields ownerField mappingField senderVar ownerVar currentVar keyParam writeVal msg1 msg2 init =
      execSourceLetCallerLetStorageAddrReqEqLetMappingReqEqLitSetMappingStop
        init ownerSlot mappingSlot writeVal msg1 msg2 := by
  simp [execCompiledLetCallerLetStorageAddrReqEqLetMappingReqEqLitSetMappingStop,
    execSourceLetCallerLetStorageAddrReqEqLetMappingReqEqLitSetMappingStop,
    compileStmts_letCallerLetStorageAddrReqEqLetMappingReqEqLitSetMappingStop_run,
    hOwner, hMapping, hne_sv_kp, hne_ov_kp, hne_ov_sv, hne_cv_kp,
    evalTStmts, defaultEvalFuel]
  by_cases hEq1 : init.env.sender = init.world.storageAddr ownerSlot
  · by_cases hEq2 : init.world.storageMap mappingSlot (init.vars.address 0) = (0 : Verity.Core.Uint256)
    · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEq1, hEq2, TVars.set, TVars.get]
    · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEq1, hEq2, TVars.set, TVars.get]
  · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEq1, TVars.set, TVars.get]

/-- Semantic-preservation for the Morpho enableLltv pattern. -/
theorem compile_letCaller_letStorageAddr_reqEq_letMappingUint_reqEqLit_reqLt_setMappingUint_stop_semantics
    (fields : List Field) (ownerField mappingField senderVar ownerVar currentVar keyParam : String)
    (ownerSlot mappingSlot : Nat) (bound writeVal : Nat) (init : TExecState)
    (msg1 msg2 msg3 : String)
    (hOwner : findFieldWithResolvedSlot fields ownerField =
      some ({ name := ownerField, ty := FieldType.address }, ownerSlot))
    (hMapping : findFieldSlot fields mappingField = some mappingSlot)
    (hne_sv_kp : senderVar ≠ keyParam)
    (hne_ov_kp : ownerVar ≠ keyParam)
    (hne_ov_sv : ownerVar ≠ senderVar)
    (hne_cv_kp : currentVar ≠ keyParam) :
    execCompiledLetCallerLetStorageAddrReqEqLetMappingUintReqEqLitReqLtSetMappingUintStop
        fields ownerField mappingField senderVar ownerVar currentVar keyParam bound writeVal
        msg1 msg2 msg3 init =
      execSourceLetCallerLetStorageAddrReqEqLetMappingUintReqEqLitReqLtSetMappingUintStop
        init ownerSlot mappingSlot bound writeVal msg1 msg2 msg3 := by
  simp [execCompiledLetCallerLetStorageAddrReqEqLetMappingUintReqEqLitReqLtSetMappingUintStop,
    execSourceLetCallerLetStorageAddrReqEqLetMappingUintReqEqLitReqLtSetMappingUintStop,
    compileStmts_letCallerLetStorageAddrReqEqLetMappingUintReqEqLitReqLtSetMappingUintStop_run,
    hOwner, hMapping, hne_sv_kp, hne_ov_kp, hne_ov_sv, hne_cv_kp,
    evalTStmts, defaultEvalFuel]
  by_cases hEq1 : init.env.sender = init.world.storageAddr ownerSlot
  · by_cases hEq2 : init.world.storageMapUint mappingSlot (init.vars.uint256 0) = (0 : Verity.Core.Uint256)
    · by_cases hEq3 : (init.vars.uint256 0 : Verity.Core.Uint256) < (bound : Verity.Core.Uint256)
      · have hNat : (init.vars.uint256 0).val < bound % Verity.Core.Uint256.modulus := by
          simpa [Verity.Core.Uint256.lt_def, Verity.Core.Uint256.val_ofNat] using hEq3
        simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEq1, hEq2, hEq3, hNat, TVars.set, TVars.get]
      · have hNat : bound % Verity.Core.Uint256.modulus ≤ (init.vars.uint256 0).val :=
          Nat.not_lt.mp (by simpa [Verity.Core.Uint256.lt_def, Verity.Core.Uint256.val_ofNat] using hEq3)
        simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEq1, hEq2, hEq3, hNat, TVars.set, TVars.get]
    · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEq1, hEq2, TVars.set, TVars.get]
  · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEq1, TVars.set, TVars.get]

/-- Semantic-preservation for the Morpho setAuthorization pattern. -/
theorem compile_letCaller_letMapping2_ite_param_req_setMapping2_stop_semantics
    (fields : List Field) (mappingField senderVar currentVar authParam boolParam : String)
    (mappingSlot : Nat) (init : TExecState) (msg1 msg2 : String)
    (hMapping : findFieldSlot fields mappingField = some mappingSlot)
    (hne_sv_bp : senderVar ≠ boolParam)
    (hne_sv_ap : senderVar ≠ authParam)
    (hne_cv_bp : currentVar ≠ boolParam)
    (hne_cv_ap : currentVar ≠ authParam)
    (hne_cv_sv : currentVar ≠ senderVar)
    (hne_bp_ap : boolParam ≠ authParam) :
    execCompiledLetCallerLetMapping2IteParamReqSetMapping2Stop
        fields mappingField senderVar currentVar authParam boolParam msg1 msg2 init =
      execSourceLetCallerLetMapping2IteParamReqSetMapping2Stop
        init mappingSlot msg1 msg2 := by
  simp [execCompiledLetCallerLetMapping2IteParamReqSetMapping2Stop,
    execSourceLetCallerLetMapping2IteParamReqSetMapping2Stop,
    compileStmts_letCallerLetMapping2IteParamReqSetMapping2Stop_run,
    hMapping, hne_sv_bp, hne_sv_ap, hne_cv_bp, hne_cv_ap, hne_cv_sv, hne_bp_ap,
    evalTStmts, defaultEvalFuel]
  by_cases hBool : init.vars.bool 1
  · by_cases hEq : init.world.storageMap2 mappingSlot init.env.sender (init.vars.address 0) = (0 : Verity.Core.Uint256)
    · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hBool, hEq, TVars.set, TVars.get]
    · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hBool, hEq, TVars.set, TVars.get]
  · by_cases hEq : init.world.storageMap2 mappingSlot init.env.sender (init.vars.address 0) = (0 : Verity.Core.Uint256)
    · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hBool, hEq, TVars.set, TVars.get]
    · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hBool, hEq, TVars.set, TVars.get]

/-- Semantic-preservation for `require (eq caller (storage ownerField)) msg ;
setStorage countField (add (storage countField) (literal n)) ; stop`. -/
theorem compile_require_caller_eq_storage_addr_setStorage_add_stop_semantics
    (fields : List Field) (ownerField countField : String)
    (ownerSlot countSlot : Nat) (init : TExecState) (n : Nat) (msg : String)
    (hOwner : findFieldWithResolvedSlot fields ownerField =
      some ({ name := ownerField, ty := FieldType.address }, ownerSlot))
    (hCount : findFieldWithResolvedSlot fields countField =
      some ({ name := countField, ty := FieldType.uint256 }, countSlot)) :
    execCompiledRequireCallerEqStorageAddrSetStorageAddStop
        fields ownerField countField init n msg =
      execSourceRequireCallerEqStorageAddrSetStorageAddStop
        init ownerSlot countSlot n msg := by
  simp [execCompiledRequireCallerEqStorageAddrSetStorageAddStop,
    execSourceRequireCallerEqStorageAddrSetStorageAddStop,
    compileStmts_require_caller_eq_storage_addr_setStorage_add_storage_literal_stop_run,
    hOwner, hCount, evalTStmts, defaultEvalFuel]
  by_cases hEq : init.env.sender = init.world.storageAddr ownerSlot
  · simp_tir_eval; simp [hEq]
  · simp_tir_eval; simp [hEq]

/-- Semantic-preservation for `require (eq caller (storage ownerField)) msg ;
setStorage countField (sub (storage countField) (literal n)) ; stop`. -/
theorem compile_require_caller_eq_storage_addr_setStorage_sub_stop_semantics
    (fields : List Field) (ownerField countField : String)
    (ownerSlot countSlot : Nat) (init : TExecState) (n : Nat) (msg : String)
    (hOwner : findFieldWithResolvedSlot fields ownerField =
      some ({ name := ownerField, ty := FieldType.address }, ownerSlot))
    (hCount : findFieldWithResolvedSlot fields countField =
      some ({ name := countField, ty := FieldType.uint256 }, countSlot)) :
    execCompiledRequireCallerEqStorageAddrSetStorageSubStop
        fields ownerField countField init n msg =
      execSourceRequireCallerEqStorageAddrSetStorageSubStop
        init ownerSlot countSlot n msg := by
  simp [execCompiledRequireCallerEqStorageAddrSetStorageSubStop,
    execSourceRequireCallerEqStorageAddrSetStorageSubStop,
    compileStmts_require_caller_eq_storage_addr_setStorage_sub_storage_literal_stop_run,
    hOwner, hCount, evalTStmts, defaultEvalFuel]
  by_cases hEq : init.env.sender = init.world.storageAddr ownerSlot
  · simp_tir_eval; simp [hEq]
  · simp_tir_eval; simp [hEq]

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
  · simp_tir_eval; simp [hEq]
  · simp_tir_eval; simp [hEq]

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
  · simp_tir_eval; simp [hEq]
  · simp_tir_eval; simp [hEq]

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
  · simp_tir_eval; simp [hEq]
  · simp_tir_eval; simp [hEq]

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
  · simp_tir_eval; simp [hEq]
  · simp_tir_eval; simp [hEq]

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
    · simp_tir_eval; simp [hEqOuter, hEqInner]
    · simp_tir_eval; simp [hEqOuter, hEqInner]
  · simp_tir_eval; simp [hEqOuter]

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
    · simp_tir_eval; simp [hEqOuter, hEqInner]
    · simp_tir_eval; simp [hEqOuter, hEqInner]
  · simp_tir_eval; simp [hEqOuter]

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
    · simp_tir_eval; simp [hEqOuter, hEqInner]
    · simp_tir_eval; simp [hEqOuter, hEqInner]
  · simp_tir_eval; simp [hEqOuter]

/-- Semantic-preservation theorem for a broader supported nested heterogeneous
branch subset:
compiling and running
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [return (literal thenVal)]
          [return (literal elseVal)]]
     [setStorage fieldName (literal outerElseWriteVal);
      return (literal outerElseRetVal)]`
matches direct source nested-branch semantics under explicit field-resolution
assumptions. -/
theorem compile_ite_eq_then_ite_eq_return_literals_then_setStorage_literal_then_return_literal_semantics
    (fields : List Field) (fieldName : String) (slot : Nat)
    (init : TExecState) (n m p q thenVal elseVal outerElseWriteVal outerElseRetVal : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledIteEqThenIteEqReturnLiteralsThenSetStorageLiteralThenReturnLiteral
        fields fieldName init n m p q thenVal elseVal outerElseWriteVal outerElseRetVal =
      execSourceIteEqThenIteEqReturnLiteralsThenSetStorageLiteralThenReturnLiteral
        init slot n m p q thenVal elseVal outerElseWriteVal outerElseRetVal := by
  simp [execCompiledIteEqThenIteEqReturnLiteralsThenSetStorageLiteralThenReturnLiteral,
    execSourceIteEqThenIteEqReturnLiteralsThenSetStorageLiteralThenReturnLiteral,
    execSourceIteEqReturnLiterals,
    compileStmts_single_ite_eq_then_ite_eq_return_literals_then_setStorage_literal_then_return_literal_run,
    execSourceSetStorageLiteral, execSourceReturnLiteral, hfind, evalTStmts, defaultEvalFuel]
  by_cases hEqOuter : (n : Verity.Core.Uint256) = (m : Verity.Core.Uint256)
  · by_cases hEqInner : (p : Verity.Core.Uint256) = (q : Verity.Core.Uint256)
    · simp_tir_eval; simp [hEqOuter, hEqInner]
    · simp_tir_eval; simp [hEqOuter, hEqInner]
  · simp_tir_eval; simp [hEqOuter]

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
    · simp_tir_eval; simp [hEqOuter, hEqInner]
    · simp_tir_eval; simp [hEqOuter, hEqInner]
  · simp_tir_eval; simp [hEqOuter]

/-- Semantic-preservation theorem for a broader supported nested heterogeneous
branch subset:
compiling and running
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [setStorage fieldName (literal thenVal)]
          [return (literal elseVal)]]
     [return (literal outerElseVal)]`
matches direct source nested-branch semantics under explicit field-resolution
assumptions. -/
theorem compile_ite_eq_then_ite_eq_setStorage_then_return_literal_then_return_literal_semantics
    (fields : List Field) (fieldName : String) (slot : Nat)
    (init : TExecState) (n m p q thenVal elseVal outerElseVal : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledIteEqThenIteEqSetStorageThenReturnLiteralThenReturnLiteral
        fields fieldName init n m p q thenVal elseVal outerElseVal =
      execSourceIteEqThenIteEqSetStorageThenReturnLiteralThenReturnLiteral
        init slot n m p q thenVal elseVal outerElseVal := by
  simp [execCompiledIteEqThenIteEqSetStorageThenReturnLiteralThenReturnLiteral,
    execSourceIteEqThenIteEqSetStorageThenReturnLiteralThenReturnLiteral,
    execSourceIteEqSetStorageThenReturnLiteral,
    compileStmts_single_ite_eq_then_ite_eq_setStorage_then_return_literal_then_return_literal_run,
    execSourceSetStorageLiteral, execSourceReturnLiteral, hfind, evalTStmts, defaultEvalFuel]
  by_cases hEqOuter : (n : Verity.Core.Uint256) = (m : Verity.Core.Uint256)
  · by_cases hEqInner : (p : Verity.Core.Uint256) = (q : Verity.Core.Uint256)
    · simp_tir_eval; simp [hEqOuter, hEqInner]
    · simp_tir_eval; simp [hEqOuter, hEqInner]
  · simp_tir_eval; simp [hEqOuter]

/-- Semantic-preservation theorem for a broader supported nested heterogeneous
branch subset:
compiling and running
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [setStorage fieldName (literal thenVal)]
          [return (literal elseVal)]]
     [setStorage fieldName (literal outerElseVal)]`
matches direct source nested-branch semantics under explicit field-resolution
assumptions. -/
theorem compile_ite_eq_then_ite_eq_setStorage_then_return_literal_then_setStorage_literal_semantics
    (fields : List Field) (fieldName : String) (slot : Nat)
    (init : TExecState) (n m p q thenVal elseVal outerElseVal : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledIteEqThenIteEqSetStorageThenReturnLiteralThenSetStorageLiteral
        fields fieldName init n m p q thenVal elseVal outerElseVal =
      execSourceIteEqThenIteEqSetStorageThenReturnLiteralThenSetStorageLiteral
        init slot n m p q thenVal elseVal outerElseVal := by
  simp [execCompiledIteEqThenIteEqSetStorageThenReturnLiteralThenSetStorageLiteral,
    execSourceIteEqThenIteEqSetStorageThenReturnLiteralThenSetStorageLiteral,
    execSourceIteEqSetStorageThenReturnLiteral,
    compileStmts_single_ite_eq_then_ite_eq_setStorage_then_return_literal_then_setStorage_literal_run,
    execSourceSetStorageLiteral, execSourceReturnLiteral, hfind, evalTStmts, defaultEvalFuel]
  by_cases hEqOuter : (n : Verity.Core.Uint256) = (m : Verity.Core.Uint256)
  · by_cases hEqInner : (p : Verity.Core.Uint256) = (q : Verity.Core.Uint256)
    · simp_tir_eval; simp [hEqOuter, hEqInner]
    · simp_tir_eval; simp [hEqOuter, hEqInner]
  · simp_tir_eval; simp [hEqOuter]

/-- Semantic-preservation theorem for a broader supported nested heterogeneous
branch subset:
compiling and running
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [return (literal thenVal)]
          [setStorage fieldName (literal elseVal)]]
     [return (literal outerElseVal)]`
matches direct source nested-branch semantics under explicit field-resolution
assumptions. -/
theorem compile_ite_eq_then_ite_eq_return_then_setStorage_literal_then_return_literal_semantics
    (fields : List Field) (fieldName : String) (slot : Nat)
    (init : TExecState) (n m p q thenVal elseVal outerElseVal : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledIteEqThenIteEqReturnThenSetStorageLiteralThenReturnLiteral
        fields fieldName init n m p q thenVal elseVal outerElseVal =
      execSourceIteEqThenIteEqReturnThenSetStorageLiteralThenReturnLiteral
        init slot n m p q thenVal elseVal outerElseVal := by
  simp [execCompiledIteEqThenIteEqReturnThenSetStorageLiteralThenReturnLiteral,
    execSourceIteEqThenIteEqReturnThenSetStorageLiteralThenReturnLiteral,
    execSourceIteEqReturnThenSetStorageLiteral,
    compileStmts_single_ite_eq_then_ite_eq_return_then_setStorage_literal_then_return_literal_run,
    execSourceSetStorageLiteral, execSourceReturnLiteral, hfind, evalTStmts, defaultEvalFuel]
  by_cases hEqOuter : (n : Verity.Core.Uint256) = (m : Verity.Core.Uint256)
  · by_cases hEqInner : (p : Verity.Core.Uint256) = (q : Verity.Core.Uint256)
    · simp_tir_eval; simp [hEqOuter, hEqInner]
    · simp_tir_eval; simp [hEqOuter, hEqInner]
  · simp_tir_eval; simp [hEqOuter]

/-- Semantic-preservation theorem for a broader supported nested heterogeneous
branch subset:
compiling and running
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [return (literal thenVal)]
          [setStorage fieldName (literal elseVal)]]
     [setStorage fieldName (literal outerElseVal)]`
matches direct source nested-branch semantics under explicit field-resolution
assumptions. -/
theorem compile_ite_eq_then_ite_eq_return_then_setStorage_literal_then_setStorage_literal_semantics
    (fields : List Field) (fieldName : String) (slot : Nat)
    (init : TExecState) (n m p q thenVal elseVal outerElseVal : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledIteEqThenIteEqReturnThenSetStorageLiteralThenSetStorageLiteral
        fields fieldName init n m p q thenVal elseVal outerElseVal =
      execSourceIteEqThenIteEqReturnThenSetStorageLiteralThenSetStorageLiteral
        init slot n m p q thenVal elseVal outerElseVal := by
  simp [execCompiledIteEqThenIteEqReturnThenSetStorageLiteralThenSetStorageLiteral,
    execSourceIteEqThenIteEqReturnThenSetStorageLiteralThenSetStorageLiteral,
    execSourceIteEqReturnThenSetStorageLiteral,
    compileStmts_single_ite_eq_then_ite_eq_return_then_setStorage_literal_then_setStorage_literal_run,
    execSourceSetStorageLiteral, execSourceReturnLiteral, hfind, evalTStmts, defaultEvalFuel]
  by_cases hEqOuter : (n : Verity.Core.Uint256) = (m : Verity.Core.Uint256)
  · by_cases hEqInner : (p : Verity.Core.Uint256) = (q : Verity.Core.Uint256)
    · simp_tir_eval; simp [hEqOuter, hEqInner]
    · simp_tir_eval; simp [hEqOuter, hEqInner]
  · simp_tir_eval; simp [hEqOuter]

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
  · simp_tir_eval; simp [hEq]
  · simp_tir_eval; simp [hEq]

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
  · simp_tir_eval; simp [hEq]
  · simp_tir_eval; simp [hEq]

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
  · simp_tir_eval; simp [hEq]

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
  · simp_tir_eval; simp [hEq]
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
          [return (literal thenVal)]
          [return (literal elseVal)]]
     [setStorage fieldName (literal outerElseWriteVal);
      return (literal outerElseRetVal)]` only on success. -/
def execSourceRequireFamilyClausesThenIteEqThenIteEqReturnLiteralsThenSetStorageLiteralThenReturnLiteral
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (slot : Nat) (n m p q thenVal elseVal outerElseWriteVal outerElseRetVal : Nat) : TExecResult :=
  match execSourceRequireLiteralGuardFamilyClauses init clauses with
  | .ok st =>
      execSourceIteEqThenIteEqReturnLiteralsThenSetStorageLiteralThenReturnLiteral
        st slot n m p q thenVal elseVal outerElseWriteVal outerElseRetVal
  | .revert reason => .revert reason

/-- Compiled semantics for the same broader supported sequencing subset:
run compiled unified `require` guard-family clause-list semantics, then run
compiled
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [return (literal thenVal)]
          [return (literal elseVal)]]
     [setStorage fieldName (literal outerElseWriteVal);
      return (literal outerElseRetVal)]` on success. -/
def execCompiledRequireFamilyClausesThenIteEqThenIteEqReturnLiteralsThenSetStorageLiteralThenReturnLiteral
    (fields : List Field) (fieldName : String) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m p q thenVal elseVal outerElseWriteVal outerElseRetVal : Nat) : TExecResult :=
  match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
  | .ok st =>
      execCompiledIteEqThenIteEqReturnLiteralsThenSetStorageLiteralThenReturnLiteral
        fields fieldName st n m p q thenVal elseVal outerElseWriteVal outerElseRetVal
  | .revert reason => .revert reason

/-- Source semantics for a broader supported sequencing subset:
run a list of supported unified `require` guard-family clauses, then perform
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [setStorage fieldName (literal thenVal)]
          [return (literal elseVal)]]
     [return (literal outerElseVal)]` only on success. -/
def execSourceRequireFamilyClausesThenIteEqThenIteEqSetStorageThenReturnLiteralThenReturnLiteral
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (slot : Nat) (n m p q thenVal elseVal outerElseVal : Nat) : TExecResult :=
  match execSourceRequireLiteralGuardFamilyClauses init clauses with
  | .ok st =>
      execSourceIteEqThenIteEqSetStorageThenReturnLiteralThenReturnLiteral
        st slot n m p q thenVal elseVal outerElseVal
  | .revert reason => .revert reason

/-- Compiled semantics for the same broader supported sequencing subset:
run compiled unified `require` guard-family clause-list semantics, then run
compiled
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [setStorage fieldName (literal thenVal)]
          [return (literal elseVal)]]
     [return (literal outerElseVal)]` on success. -/
def execCompiledRequireFamilyClausesThenIteEqThenIteEqSetStorageThenReturnLiteralThenReturnLiteral
    (fields : List Field) (fieldName : String) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m p q thenVal elseVal outerElseVal : Nat) : TExecResult :=
  match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
  | .ok st =>
      execCompiledIteEqThenIteEqSetStorageThenReturnLiteralThenReturnLiteral
        fields fieldName st n m p q thenVal elseVal outerElseVal
  | .revert reason => .revert reason

/-- Source semantics for a broader supported sequencing subset:
run a list of supported unified `require` guard-family clauses, then perform
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [setStorage fieldName (literal thenVal)]
          [return (literal elseVal)]]
     [setStorage fieldName (literal outerElseVal)]` only on success. -/
def execSourceRequireFamilyClausesThenIteEqThenIteEqSetStorageThenReturnLiteralThenSetStorageLiteral
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (slot : Nat) (n m p q thenVal elseVal outerElseVal : Nat) : TExecResult :=
  match execSourceRequireLiteralGuardFamilyClauses init clauses with
  | .ok st =>
      execSourceIteEqThenIteEqSetStorageThenReturnLiteralThenSetStorageLiteral
        st slot n m p q thenVal elseVal outerElseVal
  | .revert reason => .revert reason

/-- Compiled semantics for the same broader supported sequencing subset:
run compiled unified `require` guard-family clause-list semantics, then run
compiled
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [setStorage fieldName (literal thenVal)]
          [return (literal elseVal)]]
     [setStorage fieldName (literal outerElseVal)]` on success. -/
def execCompiledRequireFamilyClausesThenIteEqThenIteEqSetStorageThenReturnLiteralThenSetStorageLiteral
    (fields : List Field) (fieldName : String) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m p q thenVal elseVal outerElseVal : Nat) : TExecResult :=
  match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
  | .ok st =>
      execCompiledIteEqThenIteEqSetStorageThenReturnLiteralThenSetStorageLiteral
        fields fieldName st n m p q thenVal elseVal outerElseVal
  | .revert reason => .revert reason

/-- Source semantics for a broader supported sequencing subset:
run a list of supported unified `require` guard-family clauses, then perform
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [return (literal thenVal)]
          [setStorage fieldName (literal elseVal)]]
     [return (literal outerElseVal)]` only on success. -/
def execSourceRequireFamilyClausesThenIteEqThenIteEqReturnThenSetStorageLiteralThenReturnLiteral
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (slot : Nat) (n m p q thenVal elseVal outerElseVal : Nat) : TExecResult :=
  match execSourceRequireLiteralGuardFamilyClauses init clauses with
  | .ok st =>
      execSourceIteEqThenIteEqReturnThenSetStorageLiteralThenReturnLiteral
        st slot n m p q thenVal elseVal outerElseVal
  | .revert reason => .revert reason

/-- Compiled semantics for the same broader supported sequencing subset:
run compiled unified `require` guard-family clause-list semantics, then run
compiled
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [return (literal thenVal)]
          [setStorage fieldName (literal elseVal)]]
     [return (literal outerElseVal)]` on success. -/
def execCompiledRequireFamilyClausesThenIteEqThenIteEqReturnThenSetStorageLiteralThenReturnLiteral
    (fields : List Field) (fieldName : String) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m p q thenVal elseVal outerElseVal : Nat) : TExecResult :=
  match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
  | .ok st =>
      execCompiledIteEqThenIteEqReturnThenSetStorageLiteralThenReturnLiteral
        fields fieldName st n m p q thenVal elseVal outerElseVal
  | .revert reason => .revert reason

/-- Source semantics for a broader supported sequencing subset:
run a list of supported unified `require` guard-family clauses, then perform
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [return (literal thenVal)]
          [setStorage fieldName (literal elseVal)]]
     [setStorage fieldName (literal outerElseVal)]` only on success. -/
def execSourceRequireFamilyClausesThenIteEqThenIteEqReturnThenSetStorageLiteralThenSetStorageLiteral
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (slot : Nat) (n m p q thenVal elseVal outerElseVal : Nat) : TExecResult :=
  match execSourceRequireLiteralGuardFamilyClauses init clauses with
  | .ok st =>
      execSourceIteEqThenIteEqReturnThenSetStorageLiteralThenSetStorageLiteral
        st slot n m p q thenVal elseVal outerElseVal
  | .revert reason => .revert reason

/-- Compiled semantics for the same broader supported sequencing subset:
run compiled unified `require` guard-family clause-list semantics, then run
compiled
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [return (literal thenVal)]
          [setStorage fieldName (literal elseVal)]]
     [setStorage fieldName (literal outerElseVal)]` on success. -/
def execCompiledRequireFamilyClausesThenIteEqThenIteEqReturnThenSetStorageLiteralThenSetStorageLiteral
    (fields : List Field) (fieldName : String) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m p q thenVal elseVal outerElseVal : Nat) : TExecResult :=
  match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
  | .ok st =>
      execCompiledIteEqThenIteEqReturnThenSetStorageLiteralThenSetStorageLiteral
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
`ite(eq(literal,literal))` with inner return-only branches and outer false-
branch `setStorage` then `return`, compiled execution matches direct source
sequencing semantics under explicit field-resolution assumptions. -/
theorem compile_require_family_clauses_then_ite_eq_then_ite_eq_return_literals_then_setStorage_literal_then_return_literal_semantics
    (fields : List Field) (fieldName : String) (slot : Nat)
    (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m p q thenVal elseVal outerElseWriteVal outerElseRetVal : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledRequireFamilyClausesThenIteEqThenIteEqReturnLiteralsThenSetStorageLiteralThenReturnLiteral
        fields fieldName init clauses n m p q thenVal elseVal outerElseWriteVal outerElseRetVal =
      execSourceRequireFamilyClausesThenIteEqThenIteEqReturnLiteralsThenSetStorageLiteralThenReturnLiteral
        init clauses slot n m p q thenVal elseVal outerElseWriteVal outerElseRetVal := by
  simp [execCompiledRequireFamilyClausesThenIteEqThenIteEqReturnLiteralsThenSetStorageLiteralThenReturnLiteral,
    execSourceRequireFamilyClausesThenIteEqThenIteEqReturnLiteralsThenSetStorageLiteralThenReturnLiteral,
    compile_require_literal_guard_family_clauses_semantics,
    compile_ite_eq_then_ite_eq_return_literals_then_setStorage_literal_then_return_literal_semantics, hfind]
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

/-- Sequencing semantic-preservation theorem for a broader supported subset:
for unified `require` guard-family clause lists followed by nested
`ite(eq(literal,literal))` with inner storage/return branches and outer false-
branch return, compiled execution matches direct source sequencing semantics
under explicit field-resolution assumptions. -/
theorem compile_require_family_clauses_then_ite_eq_then_ite_eq_setStorage_then_return_literal_then_return_literal_semantics
    (fields : List Field) (fieldName : String) (slot : Nat)
    (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m p q thenVal elseVal outerElseVal : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledRequireFamilyClausesThenIteEqThenIteEqSetStorageThenReturnLiteralThenReturnLiteral
        fields fieldName init clauses n m p q thenVal elseVal outerElseVal =
      execSourceRequireFamilyClausesThenIteEqThenIteEqSetStorageThenReturnLiteralThenReturnLiteral
        init clauses slot n m p q thenVal elseVal outerElseVal := by
  simp [execCompiledRequireFamilyClausesThenIteEqThenIteEqSetStorageThenReturnLiteralThenReturnLiteral,
    execSourceRequireFamilyClausesThenIteEqThenIteEqSetStorageThenReturnLiteralThenReturnLiteral,
    compile_require_literal_guard_family_clauses_semantics,
    compile_ite_eq_then_ite_eq_setStorage_then_return_literal_then_return_literal_semantics, hfind]
  rfl

/-- Sequencing semantic-preservation theorem for a broader supported subset:
for unified `require` guard-family clause lists followed by nested
`ite(eq(literal,literal))` with inner storage/return branches and outer false-
branch storage write, compiled execution matches direct source sequencing
semantics under explicit field-resolution assumptions. -/
theorem compile_require_family_clauses_then_ite_eq_then_ite_eq_setStorage_then_return_literal_then_setStorage_literal_semantics
    (fields : List Field) (fieldName : String) (slot : Nat)
    (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m p q thenVal elseVal outerElseVal : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledRequireFamilyClausesThenIteEqThenIteEqSetStorageThenReturnLiteralThenSetStorageLiteral
        fields fieldName init clauses n m p q thenVal elseVal outerElseVal =
      execSourceRequireFamilyClausesThenIteEqThenIteEqSetStorageThenReturnLiteralThenSetStorageLiteral
        init clauses slot n m p q thenVal elseVal outerElseVal := by
  simp [execCompiledRequireFamilyClausesThenIteEqThenIteEqSetStorageThenReturnLiteralThenSetStorageLiteral,
    execSourceRequireFamilyClausesThenIteEqThenIteEqSetStorageThenReturnLiteralThenSetStorageLiteral,
    compile_require_literal_guard_family_clauses_semantics,
    compile_ite_eq_then_ite_eq_setStorage_then_return_literal_then_setStorage_literal_semantics, hfind]
  rfl

/-- Sequencing semantic-preservation theorem for a broader supported subset:
for unified `require` guard-family clause lists followed by nested
`ite(eq(literal,literal))` with inner return/storage branches and outer false-
branch return, compiled execution matches direct source sequencing semantics
under explicit field-resolution assumptions. -/
theorem compile_require_family_clauses_then_ite_eq_then_ite_eq_return_then_setStorage_literal_then_return_literal_semantics
    (fields : List Field) (fieldName : String) (slot : Nat)
    (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m p q thenVal elseVal outerElseVal : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledRequireFamilyClausesThenIteEqThenIteEqReturnThenSetStorageLiteralThenReturnLiteral
        fields fieldName init clauses n m p q thenVal elseVal outerElseVal =
      execSourceRequireFamilyClausesThenIteEqThenIteEqReturnThenSetStorageLiteralThenReturnLiteral
        init clauses slot n m p q thenVal elseVal outerElseVal := by
  simp [execCompiledRequireFamilyClausesThenIteEqThenIteEqReturnThenSetStorageLiteralThenReturnLiteral,
    execSourceRequireFamilyClausesThenIteEqThenIteEqReturnThenSetStorageLiteralThenReturnLiteral,
    compile_require_literal_guard_family_clauses_semantics,
    compile_ite_eq_then_ite_eq_return_then_setStorage_literal_then_return_literal_semantics, hfind]
  rfl

/-- Sequencing semantic-preservation theorem for a broader supported subset:
for unified `require` guard-family clause lists followed by nested
`ite(eq(literal,literal))` with inner return/storage branches and outer false-
branch storage write, compiled execution matches direct source sequencing
semantics under explicit field-resolution assumptions. -/
theorem compile_require_family_clauses_then_ite_eq_then_ite_eq_return_then_setStorage_literal_then_setStorage_literal_semantics
    (fields : List Field) (fieldName : String) (slot : Nat)
    (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m p q thenVal elseVal outerElseVal : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledRequireFamilyClausesThenIteEqThenIteEqReturnThenSetStorageLiteralThenSetStorageLiteral
        fields fieldName init clauses n m p q thenVal elseVal outerElseVal =
      execSourceRequireFamilyClausesThenIteEqThenIteEqReturnThenSetStorageLiteralThenSetStorageLiteral
        init clauses slot n m p q thenVal elseVal outerElseVal := by
  simp [execCompiledRequireFamilyClausesThenIteEqThenIteEqReturnThenSetStorageLiteralThenSetStorageLiteral,
    execSourceRequireFamilyClausesThenIteEqThenIteEqReturnThenSetStorageLiteralThenSetStorageLiteral,
    compile_require_literal_guard_family_clauses_semantics,
    compile_ite_eq_then_ite_eq_return_then_setStorage_literal_then_setStorage_literal_semantics, hfind]
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

/-- Source semantics for unified `require` guard-family clause lists
followed by `letVar tmp (storage field); setStorage field (add (localVar tmp) (literal m)); stop`. -/
def execSourceRequireFamilyClausesThenLetStorageSetStorageAddLocalStop
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (slot : Nat) (m : Nat) : TExecResult :=
  match execSourceRequireLiteralGuardFamilyClauses init clauses with
  | .ok st => execSourceLetStorageSetStorageAddLocalStop st slot m
  | .revert reason => .revert reason

/-- Compiled semantics for the same pattern. -/
def execCompiledRequireFamilyClausesThenLetStorageSetStorageAddLocalStop
    (fields : List Field) (fieldName tmp : String) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) (m : Nat) : TExecResult :=
  match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
  | .ok st => execCompiledLetStorageSetStorageAddLocalStop fields fieldName tmp st m
  | .revert reason => .revert reason

/-- Source semantics for unified `require` guard-family clause lists
followed by `letVar tmp (storage field); setStorage field (sub (localVar tmp) (literal m)); stop`. -/
def execSourceRequireFamilyClausesThenLetStorageSetStorageSubLocalStop
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (slot : Nat) (m : Nat) : TExecResult :=
  match execSourceRequireLiteralGuardFamilyClauses init clauses with
  | .ok st => execSourceLetStorageSetStorageSubLocalStop st slot m
  | .revert reason => .revert reason

/-- Compiled semantics for the same pattern. -/
def execCompiledRequireFamilyClausesThenLetStorageSetStorageSubLocalStop
    (fields : List Field) (fieldName tmp : String) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) (m : Nat) : TExecResult :=
  match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
  | .ok st => execCompiledLetStorageSetStorageSubLocalStop fields fieldName tmp st m
  | .revert reason => .revert reason

/-- Source semantics for unified `require` guard-family clause lists
followed by `letVar tmp (storage field); return (localVar tmp)`. -/
def execSourceRequireFamilyClausesThenLetStorageReturnLocal
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (slot : Nat) : TExecResult :=
  match execSourceRequireLiteralGuardFamilyClauses init clauses with
  | .ok st => execSourceLetStorageReturnLocal st slot
  | .revert reason => .revert reason

/-- Compiled semantics for the same pattern. -/
def execCompiledRequireFamilyClausesThenLetStorageReturnLocal
    (fields : List Field) (fieldName tmp : String) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) : TExecResult :=
  match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
  | .ok st => execCompiledLetStorageReturnLocal fields fieldName tmp st
  | .revert reason => .revert reason

/-- Source semantics for `require` clauses followed by `return (storage field)` (uint256). -/
def execSourceRequireFamilyClausesThenReturnStorage
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (slot : Nat) : TExecResult :=
  match execSourceRequireLiteralGuardFamilyClauses init clauses with
  | .ok st => execSourceReturnStorage st slot
  | .revert reason => .revert reason

/-- Compiled semantics for `require` clauses followed by `return (storage field)` (uint256). -/
def execCompiledRequireFamilyClausesThenReturnStorage
    (fields : List Field) (fieldName : String) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) : TExecResult :=
  match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
  | .ok st => execCompiledReturnStorage fields fieldName st
  | .revert reason => .revert reason

/-- Source semantics for `require` clauses followed by `return (storage field)` (address). -/
def execSourceRequireFamilyClausesThenReturnStorageAddr
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (slot : Nat) : TExecResult :=
  match execSourceRequireLiteralGuardFamilyClauses init clauses with
  | .ok st => execSourceReturnStorageAddr st slot
  | .revert reason => .revert reason

/-- Compiled semantics for `require` clauses followed by `return (storage field)` (address). -/
def execCompiledRequireFamilyClausesThenReturnStorageAddr
    (fields : List Field) (fieldName : String) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) : TExecResult :=
  match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
  | .ok st => execCompiledReturnStorageAddr fields fieldName st
  | .revert reason => .revert reason

/-- Sequencing theorem: for unified `require` guard-family clause lists followed by
`letVar tmp (storage field); setStorage field (add (localVar tmp) (literal m)); stop`,
compiled execution matches source sequencing semantics. -/
theorem compile_require_family_clauses_then_let_storage_setStorage_add_local_stop_semantics
    (fields : List Field) (fieldName tmp : String) (slot : Nat)
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause) (m : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledRequireFamilyClausesThenLetStorageSetStorageAddLocalStop
        fields fieldName tmp init clauses m =
      execSourceRequireFamilyClausesThenLetStorageSetStorageAddLocalStop
        init clauses slot m := by
  simp [execCompiledRequireFamilyClausesThenLetStorageSetStorageAddLocalStop,
    execSourceRequireFamilyClausesThenLetStorageSetStorageAddLocalStop,
    compile_require_literal_guard_family_clauses_semantics,
    compile_let_storage_setStorage_add_local_stop_semantics, hfind]

/-- Sequencing theorem: for unified `require` guard-family clause lists followed by
`letVar tmp (storage field); setStorage field (sub (localVar tmp) (literal m)); stop`,
compiled execution matches source sequencing semantics. -/
theorem compile_require_family_clauses_then_let_storage_setStorage_sub_local_stop_semantics
    (fields : List Field) (fieldName tmp : String) (slot : Nat)
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause) (m : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledRequireFamilyClausesThenLetStorageSetStorageSubLocalStop
        fields fieldName tmp init clauses m =
      execSourceRequireFamilyClausesThenLetStorageSetStorageSubLocalStop
        init clauses slot m := by
  simp [execCompiledRequireFamilyClausesThenLetStorageSetStorageSubLocalStop,
    execSourceRequireFamilyClausesThenLetStorageSetStorageSubLocalStop,
    compile_require_literal_guard_family_clauses_semantics,
    compile_let_storage_setStorage_sub_local_stop_semantics, hfind]

/-- Sequencing theorem: for unified `require` guard-family clause lists followed by
`letVar tmp (storage field); return (localVar tmp)`,
compiled execution matches source sequencing semantics. -/
theorem compile_require_family_clauses_then_let_storage_return_local_semantics
    (fields : List Field) (fieldName tmp : String) (slot : Nat)
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledRequireFamilyClausesThenLetStorageReturnLocal
        fields fieldName tmp init clauses =
      execSourceRequireFamilyClausesThenLetStorageReturnLocal
        init clauses slot := by
  simp [execCompiledRequireFamilyClausesThenLetStorageReturnLocal,
    execSourceRequireFamilyClausesThenLetStorageReturnLocal,
    compile_require_literal_guard_family_clauses_semantics,
    compile_let_storage_return_local_semantics, hfind]

/-- Sequencing theorem: `require` clauses followed by `return (storage field)` (uint256). -/
theorem compile_require_family_clauses_then_return_storage_semantics
    (fields : List Field) (fieldName : String) (slot : Nat)
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledRequireFamilyClausesThenReturnStorage
        fields fieldName init clauses =
      execSourceRequireFamilyClausesThenReturnStorage
        init clauses slot := by
  simp [execCompiledRequireFamilyClausesThenReturnStorage,
    execSourceRequireFamilyClausesThenReturnStorage,
    compile_require_literal_guard_family_clauses_semantics,
    compile_return_storage_semantics, hfind]
  split <;> simp_all

/-- Sequencing theorem: `require` clauses followed by `return (storage field)` (address). -/
theorem compile_require_family_clauses_then_return_storage_addr_semantics
    (fields : List Field) (fieldName : String) (slot : Nat)
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.address }, slot)) :
    execCompiledRequireFamilyClausesThenReturnStorageAddr
        fields fieldName init clauses =
      execSourceRequireFamilyClausesThenReturnStorageAddr
        init clauses slot := by
  simp [execCompiledRequireFamilyClausesThenReturnStorageAddr,
    execSourceRequireFamilyClausesThenReturnStorageAddr,
    compile_require_literal_guard_family_clauses_semantics,
    compile_return_storage_addr_semantics, hfind]
  split <;> simp_all

/-- Source semantics for `require` clauses followed by `return (mapping field caller)`. -/
def execSourceRequireFamilyClausesThenReturnMappingCaller
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (slot : Nat) : TExecResult :=
  match execSourceRequireLiteralGuardFamilyClauses init clauses with
  | .ok st => execSourceReturnMappingCaller st slot
  | .revert reason => .revert reason

/-- Compiled semantics for `require` clauses followed by `return (mapping field caller)`. -/
def execCompiledRequireFamilyClausesThenReturnMappingCaller
    (fields : List Field) (fieldName : String) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) : TExecResult :=
  match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
  | .ok st => execCompiledReturnMappingCaller fields fieldName st
  | .revert reason => .revert reason

/-- Sequencing theorem: `require` clauses followed by `return (mapping field caller)`. -/
theorem compile_require_family_clauses_then_return_mapping_caller_semantics
    (fields : List Field) (fieldName : String) (slot : Nat)
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (hSlot : findFieldSlot fields fieldName = some slot) :
    execCompiledRequireFamilyClausesThenReturnMappingCaller
        fields fieldName init clauses =
      execSourceRequireFamilyClausesThenReturnMappingCaller
        init clauses slot := by
  simp [execCompiledRequireFamilyClausesThenReturnMappingCaller,
    execSourceRequireFamilyClausesThenReturnMappingCaller,
    compile_require_literal_guard_family_clauses_semantics,
    compile_return_mapping_caller_semantics, hSlot]
  split <;> simp_all

/-- Source semantics for require-clauses + address storage-read + return. -/
def execSourceRequireFamilyClausesThenLetStorageAddrReturnLocal
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (slot : Nat) : TExecResult :=
  match execSourceRequireLiteralGuardFamilyClauses init clauses with
  | .ok st => execSourceLetStorageAddrReturnLocal st slot
  | .revert reason => .revert reason

/-- Compiled semantics for the same pattern. -/
def execCompiledRequireFamilyClausesThenLetStorageAddrReturnLocal
    (fields : List Field) (fieldName tmp : String) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) : TExecResult :=
  match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
  | .ok st => execCompiledLetStorageAddrReturnLocal fields fieldName tmp st
  | .revert reason => .revert reason

/-- Sequencing theorem: require clauses + address storage-read + return. -/
theorem compile_require_family_clauses_then_let_storage_addr_return_local_semantics
    (fields : List Field) (fieldName tmp : String) (slot : Nat)
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.address }, slot)) :
    execCompiledRequireFamilyClausesThenLetStorageAddrReturnLocal
        fields fieldName tmp init clauses =
      execSourceRequireFamilyClausesThenLetStorageAddrReturnLocal
        init clauses slot := by
  simp [execCompiledRequireFamilyClausesThenLetStorageAddrReturnLocal,
    execSourceRequireFamilyClausesThenLetStorageAddrReturnLocal,
    compile_require_literal_guard_family_clauses_semantics,
    compile_let_storage_addr_return_local_semantics, hfind]

/-- Source semantics for require-clauses + mapping(param) read + return. -/
def execSourceRequireFamilyClausesThenLetMappingParamReturnLocal
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (slot : Nat) : TExecResult :=
  match execSourceRequireLiteralGuardFamilyClauses init clauses with
  | .ok st => execSourceLetMappingParamReturnLocal st slot
  | .revert reason => .revert reason

/-- Compiled semantics for the same pattern. -/
def execCompiledRequireFamilyClausesThenLetMappingParamReturnLocal
    (fields : List Field) (fieldName paramName tmp : String) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) : TExecResult :=
  match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
  | .ok st => execCompiledLetMappingParamReturnLocal fields fieldName paramName tmp st
  | .revert reason => .revert reason

/-- Sequencing theorem: require clauses + mapping(param) read + return. -/
theorem compile_require_family_clauses_then_let_mapping_param_return_local_semantics
    (fields : List Field) (fieldName paramName tmp : String) (slot : Nat)
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (hSlot : findFieldSlot fields fieldName = some slot) :
    execCompiledRequireFamilyClausesThenLetMappingParamReturnLocal
        fields fieldName paramName tmp init clauses =
      execSourceRequireFamilyClausesThenLetMappingParamReturnLocal
        init clauses slot := by
  simp [execCompiledRequireFamilyClausesThenLetMappingParamReturnLocal,
    execSourceRequireFamilyClausesThenLetMappingParamReturnLocal,
    compile_require_literal_guard_family_clauses_semantics,
    compile_let_mapping_param_return_local_semantics, hSlot]

/-- Source semantics for require-clauses + mapping2(param1, param2) read + return. -/
def execSourceRequireFamilyClausesThenLetMapping2ParamsReturnLocal
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (slot : Nat) : TExecResult :=
  match execSourceRequireLiteralGuardFamilyClauses init clauses with
  | .ok st => execSourceLetMapping2ParamsReturnLocal st slot
  | .revert reason => .revert reason

/-- Compiled semantics for the same pattern. -/
def execCompiledRequireFamilyClausesThenLetMapping2ParamsReturnLocal
    (fields : List Field) (fieldName p1 p2 tmp : String) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) : TExecResult :=
  match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
  | .ok st => execCompiledLetMapping2ParamsReturnLocal fields fieldName p1 p2 tmp st
  | .revert reason => .revert reason

/-- Sequencing theorem: require clauses + mapping2(param1, param2) read + return. -/
theorem compile_require_family_clauses_then_let_mapping2_params_return_local_semantics
    (fields : List Field) (fieldName p1 p2 tmp : String) (slot : Nat)
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (hSlot : findFieldSlot fields fieldName = some slot)
    (hp : p1 ≠ p2) :
    execCompiledRequireFamilyClausesThenLetMapping2ParamsReturnLocal
        fields fieldName p1 p2 tmp init clauses =
      execSourceRequireFamilyClausesThenLetMapping2ParamsReturnLocal
        init clauses slot := by
  simp [execCompiledRequireFamilyClausesThenLetMapping2ParamsReturnLocal,
    execSourceRequireFamilyClausesThenLetMapping2ParamsReturnLocal,
    compile_require_literal_guard_family_clauses_semantics,
    compile_let_mapping2_params_return_local_semantics, hSlot, hp]

/-- Source semantics for require-clauses + let caller + setMapping2 + stop. -/
def execSourceRequireFamilyClausesThenLetCallerSetMapping2Stop
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (slot : Nat) : TExecResult :=
  match execSourceRequireLiteralGuardFamilyClauses init clauses with
  | .ok st => execSourceLetCallerSetMapping2Stop st slot
  | .revert reason => .revert reason

/-- Compiled semantics for the same pattern. -/
def execCompiledRequireFamilyClausesThenLetCallerSetMapping2Stop
    (fields : List Field) (fieldName senderVar p1 p2 : String) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) : TExecResult :=
  match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
  | .ok st => execCompiledLetCallerSetMapping2Stop fields fieldName senderVar p1 p2 st
  | .revert reason => .revert reason

/-- Sequencing theorem: require clauses + let caller + setMapping2 + stop. -/
theorem compile_require_family_clauses_then_let_caller_setMapping2_stop_semantics
    (fields : List Field) (fieldName senderVar p1 p2 : String) (slot : Nat)
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (hSlot : findFieldSlot fields fieldName = some slot)
    (h1 : senderVar ≠ p2) (h2 : senderVar ≠ p1) (h3 : p2 ≠ p1)
    (h4 : p1 ≠ p2) (h5 : p1 ≠ senderVar) (h6 : p2 ≠ senderVar) :
    execCompiledRequireFamilyClausesThenLetCallerSetMapping2Stop
        fields fieldName senderVar p1 p2 init clauses =
      execSourceRequireFamilyClausesThenLetCallerSetMapping2Stop
        init clauses slot := by
  simp [execCompiledRequireFamilyClausesThenLetCallerSetMapping2Stop,
    execSourceRequireFamilyClausesThenLetCallerSetMapping2Stop,
    compile_require_literal_guard_family_clauses_semantics,
    compile_let_caller_setMapping2_stop_semantics, hSlot,
    h1, h2, h3, h4, h5, h6]

/-- Source semantics for require-clauses + letMappingUintParam + return. -/
def execSourceRequireFamilyClausesThenLetMappingUintParamReturnLocal
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (slot : Nat) : TExecResult :=
  match execSourceRequireLiteralGuardFamilyClauses init clauses with
  | .ok st => execSourceLetMappingUintParamReturnLocal st slot
  | .revert reason => .revert reason

/-- Compiled semantics for require-clauses + letMappingUintParam + return. -/
def execCompiledRequireFamilyClausesThenLetMappingUintParamReturnLocal
    (fields : List Field) (fieldName paramName tmp : String) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) : TExecResult :=
  match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
  | .ok st => execCompiledLetMappingUintParamReturnLocal fields fieldName paramName tmp st
  | .revert reason => .revert reason

/-- Sequencing: require clauses + mappingUint(param) read + return. -/
theorem compile_require_family_clauses_then_let_mappingUint_param_return_local_semantics
    (fields : List Field) (fieldName paramName tmp : String) (slot : Nat)
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (hSlot : findFieldSlot fields fieldName = some slot) :
    execCompiledRequireFamilyClausesThenLetMappingUintParamReturnLocal
        fields fieldName paramName tmp init clauses =
      execSourceRequireFamilyClausesThenLetMappingUintParamReturnLocal
        init clauses slot := by
  simp [execCompiledRequireFamilyClausesThenLetMappingUintParamReturnLocal,
    execSourceRequireFamilyClausesThenLetMappingUintParamReturnLocal,
    compile_require_literal_guard_family_clauses_semantics,
    compile_let_mappingUint_param_return_local_semantics, hSlot]

/-- Source semantics for require-clauses + setMappingUint(params) + stop. -/
def execSourceRequireFamilyClausesThenSetMappingUintParamsStop
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (slot : Nat) : TExecResult :=
  match execSourceRequireLiteralGuardFamilyClauses init clauses with
  | .ok st => execSourceSetMappingUintParamsStop st slot
  | .revert reason => .revert reason

/-- Compiled semantics for require-clauses + setMappingUint(params) + stop. -/
def execCompiledRequireFamilyClausesThenSetMappingUintParamsStop
    (fields : List Field) (fieldName p1 p2 : String) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) : TExecResult :=
  match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
  | .ok st => execCompiledSetMappingUintParamsStop fields fieldName p1 p2 st
  | .revert reason => .revert reason

/-- Sequencing: require clauses + setMappingUint(params) + stop. -/
theorem compile_require_family_clauses_then_setMappingUint_params_stop_semantics
    (fields : List Field) (fieldName p1 p2 : String) (slot : Nat)
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (hSlot : findFieldSlot fields fieldName = some slot)
    (hp : p1 ≠ p2) :
    execCompiledRequireFamilyClausesThenSetMappingUintParamsStop
        fields fieldName p1 p2 init clauses =
      execSourceRequireFamilyClausesThenSetMappingUintParamsStop
        init clauses slot := by
  simp [execCompiledRequireFamilyClausesThenSetMappingUintParamsStop,
    execSourceRequireFamilyClausesThenSetMappingUintParamsStop,
    compile_require_literal_guard_family_clauses_semantics,
    compile_setMappingUint_params_stop_semantics, hSlot, hp]
  cases h : execSourceRequireLiteralGuardFamilyClauses init clauses <;> rfl

/-- Source semantics for require-clauses + requireCallerEqStorageAddr + setStorage(add) + stop. -/
def execSourceRequireFamilyClausesThenRequireCallerEqStorageAddrSetStorageAddStop
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (ownerSlot countSlot : Nat) (n : Nat) (msg : String) : TExecResult :=
  match execSourceRequireLiteralGuardFamilyClauses init clauses with
  | .ok st => execSourceRequireCallerEqStorageAddrSetStorageAddStop st ownerSlot countSlot n msg
  | .revert reason => .revert reason

/-- Compiled semantics for require-clauses + requireCallerEqStorageAddr + setStorage(add) + stop. -/
def execCompiledRequireFamilyClausesThenRequireCallerEqStorageAddrSetStorageAddStop
    (fields : List Field) (ownerField countField : String)
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (n : Nat) (msg : String) : TExecResult :=
  match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
  | .ok st => execCompiledRequireCallerEqStorageAddrSetStorageAddStop fields ownerField countField st n msg
  | .revert reason => .revert reason

/-- Sequencing: require-clauses + requireCallerEqStorageAddr + setStorage(add) + stop. -/
theorem compile_require_family_clauses_then_require_caller_eq_storage_addr_setStorage_add_stop_semantics
    (fields : List Field) (ownerField countField : String)
    (ownerSlot countSlot : Nat) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) (n : Nat) (msg : String)
    (hOwner : findFieldWithResolvedSlot fields ownerField =
      some ({ name := ownerField, ty := FieldType.address }, ownerSlot))
    (hCount : findFieldWithResolvedSlot fields countField =
      some ({ name := countField, ty := FieldType.uint256 }, countSlot)) :
    execCompiledRequireFamilyClausesThenRequireCallerEqStorageAddrSetStorageAddStop
        fields ownerField countField init clauses n msg =
      execSourceRequireFamilyClausesThenRequireCallerEqStorageAddrSetStorageAddStop
        init clauses ownerSlot countSlot n msg := by
  simp [execCompiledRequireFamilyClausesThenRequireCallerEqStorageAddrSetStorageAddStop,
    execSourceRequireFamilyClausesThenRequireCallerEqStorageAddrSetStorageAddStop,
    compile_require_literal_guard_family_clauses_semantics,
    compile_require_caller_eq_storage_addr_setStorage_add_stop_semantics, hOwner, hCount]
  split <;> simp_all

/-- Source semantics for require-clauses + requireCallerEqStorageAddr + setStorage(sub) + stop. -/
def execSourceRequireFamilyClausesThenRequireCallerEqStorageAddrSetStorageSubStop
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (ownerSlot countSlot : Nat) (n : Nat) (msg : String) : TExecResult :=
  match execSourceRequireLiteralGuardFamilyClauses init clauses with
  | .ok st => execSourceRequireCallerEqStorageAddrSetStorageSubStop st ownerSlot countSlot n msg
  | .revert reason => .revert reason

/-- Compiled semantics for require-clauses + requireCallerEqStorageAddr + setStorage(sub) + stop. -/
def execCompiledRequireFamilyClausesThenRequireCallerEqStorageAddrSetStorageSubStop
    (fields : List Field) (ownerField countField : String)
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (n : Nat) (msg : String) : TExecResult :=
  match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
  | .ok st => execCompiledRequireCallerEqStorageAddrSetStorageSubStop fields ownerField countField st n msg
  | .revert reason => .revert reason

/-- Sequencing: require-clauses + requireCallerEqStorageAddr + setStorage(sub) + stop. -/
theorem compile_require_family_clauses_then_require_caller_eq_storage_addr_setStorage_sub_stop_semantics
    (fields : List Field) (ownerField countField : String)
    (ownerSlot countSlot : Nat) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) (n : Nat) (msg : String)
    (hOwner : findFieldWithResolvedSlot fields ownerField =
      some ({ name := ownerField, ty := FieldType.address }, ownerSlot))
    (hCount : findFieldWithResolvedSlot fields countField =
      some ({ name := countField, ty := FieldType.uint256 }, countSlot)) :
    execCompiledRequireFamilyClausesThenRequireCallerEqStorageAddrSetStorageSubStop
        fields ownerField countField init clauses n msg =
      execSourceRequireFamilyClausesThenRequireCallerEqStorageAddrSetStorageSubStop
        init clauses ownerSlot countSlot n msg := by
  simp [execCompiledRequireFamilyClausesThenRequireCallerEqStorageAddrSetStorageSubStop,
    execSourceRequireFamilyClausesThenRequireCallerEqStorageAddrSetStorageSubStop,
    compile_require_literal_guard_family_clauses_semantics,
    compile_require_caller_eq_storage_addr_setStorage_sub_stop_semantics, hOwner, hCount]
  split <;> simp_all

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
  | iteEqThenIteEqReturnLiteralsThenSetStorageLiteralThenReturnLiteral
      (fieldName : String) (slot : Nat)
      (n m p q thenVal elseVal outerElseWriteVal outerElseRetVal : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | iteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral
      (fieldName : String) (slot : Nat)
      (n m p q thenVal elseVal outerElseVal : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | iteEqThenIteEqSetStorageThenReturnLiteralThenReturnLiteral
      (fieldName : String) (slot : Nat)
      (n m p q thenVal elseVal outerElseVal : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | iteEqThenIteEqSetStorageThenReturnLiteralThenSetStorageLiteral
      (fieldName : String) (slot : Nat)
      (n m p q thenVal elseVal outerElseVal : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | iteEqThenIteEqReturnThenSetStorageLiteralThenReturnLiteral
      (fieldName : String) (slot : Nat)
      (n m p q thenVal elseVal outerElseVal : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | iteEqThenIteEqReturnThenSetStorageLiteralThenSetStorageLiteral
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
  | letStorageSetStorageAddLocalStop
      (fieldName tmp : String) (slot : Nat) (m : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | letStorageSetStorageSubLocalStop
      (fieldName tmp : String) (slot : Nat) (m : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | letStorageReturnLocal
      (fieldName tmp : String) (slot : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | returnStorage
      (fieldName : String) (slot : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | returnStorageAddr
      (fieldName : String) (slot : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.address }, slot))
  | requireCallerEqStorageAddrSetStorageAddStop
      (ownerField countField msg : String) (ownerSlot countSlot : Nat) (n : Nat)
      (hOwner : findFieldWithResolvedSlot fields ownerField =
        some ({ name := ownerField, ty := FieldType.address }, ownerSlot))
      (hCount : findFieldWithResolvedSlot fields countField =
        some ({ name := countField, ty := FieldType.uint256 }, countSlot))
  | requireCallerEqStorageAddrSetStorageSubStop
      (ownerField countField msg : String) (ownerSlot countSlot : Nat) (n : Nat)
      (hOwner : findFieldWithResolvedSlot fields ownerField =
        some ({ name := ownerField, ty := FieldType.address }, ownerSlot))
      (hCount : findFieldWithResolvedSlot fields countField =
        some ({ name := countField, ty := FieldType.uint256 }, countSlot))
  | returnMappingCaller
      (fieldName : String) (slot : Nat)
      (hSlot : findFieldSlot fields fieldName = some slot)
  | letStorageAddrReturnLocal
      (fieldName tmp : String) (slot : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.address }, slot))
  | letMappingParamReturnLocal
      (fieldName paramName tmp : String) (slot : Nat)
      (hSlot : findFieldSlot fields fieldName = some slot)
  | letMapping2ParamsReturnLocal
      (fieldName p1 p2 tmp : String) (slot : Nat)
      (hSlot : findFieldSlot fields fieldName = some slot)
      (hp : p1 ≠ p2)
  | letCallerSetMapping2Stop
      (fieldName senderVar p1 p2 : String) (slot : Nat)
      (hSlot : findFieldSlot fields fieldName = some slot)
      (h1 : senderVar ≠ p2) (h2 : senderVar ≠ p1) (h3 : p2 ≠ p1)
      (h4 : p1 ≠ p2) (h5 : p1 ≠ senderVar) (h6 : p2 ≠ senderVar)
  | letMappingUintParamReturnLocal
      (fieldName paramName tmp : String) (slot : Nat)
      (hSlot : findFieldSlot fields fieldName = some slot)
  | setMappingUintParamsStop
      (fieldName p1 p2 : String) (slot : Nat)
      (hSlot : findFieldSlot fields fieldName = some slot)
      (hp : p1 ≠ p2)
  -- Morpho Blue admin function patterns (monolithic tails)
  | letCallerLetStorageAddrReqEqReqNeqSetStorageAddrParamStop
      (ownerField senderVar ownerVar paramName msg1 msg2 : String) (ownerSlot : Nat)
      (hOwner : findFieldWithResolvedSlot fields ownerField =
        some ({ name := ownerField, ty := FieldType.address }, ownerSlot))
      (hne_sv_p : senderVar ≠ paramName)
      (hne_ov_p : ownerVar ≠ paramName)
      (hne_ov_sv : ownerVar ≠ senderVar)
  | letCallerLetStorageAddrReqEqLetMappingReqEqLitSetMappingStop
      (ownerField mappingField senderVar ownerVar currentVar keyParam : String)
      (ownerSlot mappingSlot : Nat) (writeVal : Nat) (msg1 msg2 : String)
      (hOwner : findFieldWithResolvedSlot fields ownerField =
        some ({ name := ownerField, ty := FieldType.address }, ownerSlot))
      (hMapping : findFieldSlot fields mappingField = some mappingSlot)
      (hne_sv_kp : senderVar ≠ keyParam)
      (hne_ov_kp : ownerVar ≠ keyParam)
      (hne_ov_sv : ownerVar ≠ senderVar)
      (hne_cv_kp : currentVar ≠ keyParam)
  | letCallerLetStorageAddrReqEqLetMappingUintReqEqLitReqLtSetMappingUintStop
      (ownerField mappingField senderVar ownerVar currentVar keyParam : String)
      (ownerSlot mappingSlot : Nat) (bound writeVal : Nat) (msg1 msg2 msg3 : String)
      (hOwner : findFieldWithResolvedSlot fields ownerField =
        some ({ name := ownerField, ty := FieldType.address }, ownerSlot))
      (hMapping : findFieldSlot fields mappingField = some mappingSlot)
      (hne_sv_kp : senderVar ≠ keyParam)
      (hne_ov_kp : ownerVar ≠ keyParam)
      (hne_ov_sv : ownerVar ≠ senderVar)
      (hne_cv_kp : currentVar ≠ keyParam)
  | letCallerLetMapping2IteParamReqSetMapping2Stop
      (mappingField senderVar currentVar authParam boolParam msg1 msg2 : String) (mappingSlot : Nat)
      (hMapping : findFieldSlot fields mappingField = some mappingSlot)
      (hne_sv_bp : senderVar ≠ boolParam)
      (hne_sv_ap : senderVar ≠ authParam)
      (hne_cv_bp : currentVar ≠ boolParam)
      (hne_cv_ap : currentVar ≠ authParam)
      (hne_cv_sv : currentVar ≠ senderVar)
      (hne_bp_ap : boolParam ≠ authParam)

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
  | .iteEqThenIteEqReturnLiteralsThenSetStorageLiteralThenReturnLiteral
      _ slot n m p q thenVal elseVal outerElseWriteVal outerElseRetVal _ =>
      execSourceRequireFamilyClausesThenIteEqThenIteEqReturnLiteralsThenSetStorageLiteralThenReturnLiteral
        init clauses slot n m p q thenVal elseVal outerElseWriteVal outerElseRetVal
  | .iteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral
      _ slot n m p q thenVal elseVal outerElseVal _ =>
      execSourceRequireFamilyClausesThenIteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral
        init clauses slot n m p q thenVal elseVal outerElseVal
  | .iteEqThenIteEqSetStorageThenReturnLiteralThenReturnLiteral
      _ slot n m p q thenVal elseVal outerElseVal _ =>
      execSourceRequireFamilyClausesThenIteEqThenIteEqSetStorageThenReturnLiteralThenReturnLiteral
        init clauses slot n m p q thenVal elseVal outerElseVal
  | .iteEqThenIteEqSetStorageThenReturnLiteralThenSetStorageLiteral
      _ slot n m p q thenVal elseVal outerElseVal _ =>
      execSourceRequireFamilyClausesThenIteEqThenIteEqSetStorageThenReturnLiteralThenSetStorageLiteral
        init clauses slot n m p q thenVal elseVal outerElseVal
  | .iteEqThenIteEqReturnThenSetStorageLiteralThenReturnLiteral
      _ slot n m p q thenVal elseVal outerElseVal _ =>
      execSourceRequireFamilyClausesThenIteEqThenIteEqReturnThenSetStorageLiteralThenReturnLiteral
        init clauses slot n m p q thenVal elseVal outerElseVal
  | .iteEqThenIteEqReturnThenSetStorageLiteralThenSetStorageLiteral
      _ slot n m p q thenVal elseVal outerElseVal _ =>
      execSourceRequireFamilyClausesThenIteEqThenIteEqReturnThenSetStorageLiteralThenSetStorageLiteral
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
  | .letStorageSetStorageAddLocalStop _ _ slot m _ =>
      execSourceRequireFamilyClausesThenLetStorageSetStorageAddLocalStop init clauses slot m
  | .letStorageSetStorageSubLocalStop _ _ slot m _ =>
      execSourceRequireFamilyClausesThenLetStorageSetStorageSubLocalStop init clauses slot m
  | .letStorageReturnLocal _ _ slot _ =>
      execSourceRequireFamilyClausesThenLetStorageReturnLocal init clauses slot
  | .returnStorage _ slot _ =>
      execSourceRequireFamilyClausesThenReturnStorage init clauses slot
  | .returnStorageAddr _ slot _ =>
      execSourceRequireFamilyClausesThenReturnStorageAddr init clauses slot
  | .requireCallerEqStorageAddrSetStorageAddStop _ _ msg ownerSlot countSlot n _ _ =>
      execSourceRequireFamilyClausesThenRequireCallerEqStorageAddrSetStorageAddStop
        init clauses ownerSlot countSlot n msg
  | .requireCallerEqStorageAddrSetStorageSubStop _ _ msg ownerSlot countSlot n _ _ =>
      execSourceRequireFamilyClausesThenRequireCallerEqStorageAddrSetStorageSubStop
        init clauses ownerSlot countSlot n msg
  | .returnMappingCaller _ slot _ =>
      execSourceRequireFamilyClausesThenReturnMappingCaller init clauses slot
  | .letStorageAddrReturnLocal _ _ slot _ =>
      execSourceRequireFamilyClausesThenLetStorageAddrReturnLocal init clauses slot
  | .letMappingParamReturnLocal _ _ _ slot _ =>
      execSourceRequireFamilyClausesThenLetMappingParamReturnLocal init clauses slot
  | .letMapping2ParamsReturnLocal _ _ _ _ slot _ _ =>
      execSourceRequireFamilyClausesThenLetMapping2ParamsReturnLocal init clauses slot
  | .letCallerSetMapping2Stop _ _ _ _ slot _ _ _ _ _ _ _ =>
      execSourceRequireFamilyClausesThenLetCallerSetMapping2Stop init clauses slot
  | .letMappingUintParamReturnLocal _ _ _ slot _ =>
      execSourceRequireFamilyClausesThenLetMappingUintParamReturnLocal init clauses slot
  | .setMappingUintParamsStop _ _ _ slot _ _ =>
      execSourceRequireFamilyClausesThenSetMappingUintParamsStop init clauses slot
  -- Morpho admin tails: for these monolithic patterns, the require-clause prefix is empty,
  -- so the source semantics just runs the tail directly on init (no clause processing needed).
  | .letCallerLetStorageAddrReqEqReqNeqSetStorageAddrParamStop _ _ _ _ msg1 msg2 ownerSlot _ _ _ _ =>
      match execSourceRequireLiteralGuardFamilyClauses init clauses with
      | .ok st => execSourceLetCallerLetStorageAddrReqEqReqNeqSetStorageAddrParamStop st ownerSlot msg1 msg2
      | .revert reason => .revert reason
  | .letCallerLetStorageAddrReqEqLetMappingReqEqLitSetMappingStop _ _ _ _ _ _
      ownerSlot mappingSlot writeVal msg1 msg2 _ _ _ _ _ _ =>
      match execSourceRequireLiteralGuardFamilyClauses init clauses with
      | .ok st => execSourceLetCallerLetStorageAddrReqEqLetMappingReqEqLitSetMappingStop
          st ownerSlot mappingSlot writeVal msg1 msg2
      | .revert reason => .revert reason
  | .letCallerLetStorageAddrReqEqLetMappingUintReqEqLitReqLtSetMappingUintStop _ _ _ _ _ _
      ownerSlot mappingSlot bound writeVal msg1 msg2 msg3 _ _ _ _ _ _ =>
      match execSourceRequireLiteralGuardFamilyClauses init clauses with
      | .ok st => execSourceLetCallerLetStorageAddrReqEqLetMappingUintReqEqLitReqLtSetMappingUintStop
          st ownerSlot mappingSlot bound writeVal msg1 msg2 msg3
      | .revert reason => .revert reason
  | .letCallerLetMapping2IteParamReqSetMapping2Stop _ _ _ _ _ msg1 msg2 mappingSlot _ _ _ _ _ _ _ =>
      match execSourceRequireLiteralGuardFamilyClauses init clauses with
      | .ok st => execSourceLetCallerLetMapping2IteParamReqSetMapping2Stop
          st mappingSlot msg1 msg2
      | .revert reason => .revert reason

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
  | .iteEqThenIteEqReturnLiteralsThenSetStorageLiteralThenReturnLiteral
      fieldName _ n m p q thenVal elseVal outerElseWriteVal outerElseRetVal _ =>
      execCompiledRequireFamilyClausesThenIteEqThenIteEqReturnLiteralsThenSetStorageLiteralThenReturnLiteral
        fields fieldName init clauses n m p q thenVal elseVal outerElseWriteVal outerElseRetVal
  | .iteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral
      fieldName _ n m p q thenVal elseVal outerElseVal _ =>
      execCompiledRequireFamilyClausesThenIteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral
        fields fieldName init clauses n m p q thenVal elseVal outerElseVal
  | .iteEqThenIteEqSetStorageThenReturnLiteralThenReturnLiteral
      fieldName _ n m p q thenVal elseVal outerElseVal _ =>
      execCompiledRequireFamilyClausesThenIteEqThenIteEqSetStorageThenReturnLiteralThenReturnLiteral
        fields fieldName init clauses n m p q thenVal elseVal outerElseVal
  | .iteEqThenIteEqSetStorageThenReturnLiteralThenSetStorageLiteral
      fieldName _ n m p q thenVal elseVal outerElseVal _ =>
      execCompiledRequireFamilyClausesThenIteEqThenIteEqSetStorageThenReturnLiteralThenSetStorageLiteral
        fields fieldName init clauses n m p q thenVal elseVal outerElseVal
  | .iteEqThenIteEqReturnThenSetStorageLiteralThenReturnLiteral
      fieldName _ n m p q thenVal elseVal outerElseVal _ =>
      execCompiledRequireFamilyClausesThenIteEqThenIteEqReturnThenSetStorageLiteralThenReturnLiteral
        fields fieldName init clauses n m p q thenVal elseVal outerElseVal
  | .iteEqThenIteEqReturnThenSetStorageLiteralThenSetStorageLiteral
      fieldName _ n m p q thenVal elseVal outerElseVal _ =>
      execCompiledRequireFamilyClausesThenIteEqThenIteEqReturnThenSetStorageLiteralThenSetStorageLiteral
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
  | .letStorageSetStorageAddLocalStop fieldName tmp _ m _ =>
      execCompiledRequireFamilyClausesThenLetStorageSetStorageAddLocalStop
        fields fieldName tmp init clauses m
  | .letStorageSetStorageSubLocalStop fieldName tmp _ m _ =>
      execCompiledRequireFamilyClausesThenLetStorageSetStorageSubLocalStop
        fields fieldName tmp init clauses m
  | .letStorageReturnLocal fieldName tmp _ _ =>
      execCompiledRequireFamilyClausesThenLetStorageReturnLocal
        fields fieldName tmp init clauses
  | .returnStorage fieldName _ _ =>
      execCompiledRequireFamilyClausesThenReturnStorage
        fields fieldName init clauses
  | .returnStorageAddr fieldName _ _ =>
      execCompiledRequireFamilyClausesThenReturnStorageAddr
        fields fieldName init clauses
  | .requireCallerEqStorageAddrSetStorageAddStop ownerField countField msg _ _ n _ _ =>
      execCompiledRequireFamilyClausesThenRequireCallerEqStorageAddrSetStorageAddStop
        fields ownerField countField init clauses n msg
  | .requireCallerEqStorageAddrSetStorageSubStop ownerField countField msg _ _ n _ _ =>
      execCompiledRequireFamilyClausesThenRequireCallerEqStorageAddrSetStorageSubStop
        fields ownerField countField init clauses n msg
  | .returnMappingCaller fieldName _ _ =>
      execCompiledRequireFamilyClausesThenReturnMappingCaller
        fields fieldName init clauses
  | .letStorageAddrReturnLocal fieldName tmp _ _ =>
      execCompiledRequireFamilyClausesThenLetStorageAddrReturnLocal
        fields fieldName tmp init clauses
  | .letMappingParamReturnLocal fieldName paramName tmp _ _ =>
      execCompiledRequireFamilyClausesThenLetMappingParamReturnLocal
        fields fieldName paramName tmp init clauses
  | .letMapping2ParamsReturnLocal fieldName p1 p2 tmp _ _ _ =>
      execCompiledRequireFamilyClausesThenLetMapping2ParamsReturnLocal
        fields fieldName p1 p2 tmp init clauses
  | .letCallerSetMapping2Stop fieldName senderVar p1 p2 _ _ _ _ _ _ _ _ =>
      execCompiledRequireFamilyClausesThenLetCallerSetMapping2Stop
        fields fieldName senderVar p1 p2 init clauses
  | .letMappingUintParamReturnLocal fieldName paramName tmp _ _ =>
      execCompiledRequireFamilyClausesThenLetMappingUintParamReturnLocal
        fields fieldName paramName tmp init clauses
  | .setMappingUintParamsStop fieldName p1 p2 _ _ _ =>
      execCompiledRequireFamilyClausesThenSetMappingUintParamsStop
        fields fieldName p1 p2 init clauses
  -- Morpho admin tails
  | .letCallerLetStorageAddrReqEqReqNeqSetStorageAddrParamStop
      ownerField senderVar ownerVar paramName msg1 msg2 _ _ _ _ _ =>
      match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
      | .ok st => execCompiledLetCallerLetStorageAddrReqEqReqNeqSetStorageAddrParamStop
          fields ownerField senderVar ownerVar paramName msg1 msg2 st
      | .revert reason => .revert reason
  | .letCallerLetStorageAddrReqEqLetMappingReqEqLitSetMappingStop
      ownerField mappingField senderVar ownerVar currentVar keyParam _ _ writeVal msg1 msg2
      _ _ _ _ _ _ =>
      match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
      | .ok st => execCompiledLetCallerLetStorageAddrReqEqLetMappingReqEqLitSetMappingStop
          fields ownerField mappingField senderVar ownerVar currentVar keyParam writeVal msg1 msg2 st
      | .revert reason => .revert reason
  | .letCallerLetStorageAddrReqEqLetMappingUintReqEqLitReqLtSetMappingUintStop
      ownerField mappingField senderVar ownerVar currentVar keyParam _ _ bound writeVal msg1 msg2 msg3
      _ _ _ _ _ _ =>
      match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
      | .ok st => execCompiledLetCallerLetStorageAddrReqEqLetMappingUintReqEqLitReqLtSetMappingUintStop
          fields ownerField mappingField senderVar ownerVar currentVar keyParam bound writeVal msg1 msg2 msg3 st
      | .revert reason => .revert reason
  | .letCallerLetMapping2IteParamReqSetMapping2Stop
      mappingField senderVar currentVar authParam boolParam msg1 msg2 _ _ _ _ _ _ _ _ =>
      match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
      | .ok st => execCompiledLetCallerLetMapping2IteParamReqSetMapping2Stop
          fields mappingField senderVar currentVar authParam boolParam msg1 msg2 st
      | .revert reason => .revert reason

/-- Generic sequencing semantic-preservation theorem over the supported tail
family after unified `require` guard-family clause lists. -/
syntax "simpa_require_family_tail" " using " term : tactic

macro_rules
  | `(tactic| simpa_require_family_tail using $h) =>
      `(tactic| simpa [execCompiledRequireFamilyClausesThenTail, execSourceRequireFamilyClausesThenTail] using $h)

theorem compile_require_family_clauses_then_tail_semantics
    (fields : List Field) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (tail : RequireFamilyClausesTail fields) :
    execCompiledRequireFamilyClausesThenTail fields init clauses tail =
      execSourceRequireFamilyClausesThenTail fields init clauses tail := by
  cases tail with
  | noOp =>
      simpa_require_family_tail using compile_require_family_clauses_then_noop_semantics fields init clauses
  | setStorageLiteral fieldName slot writeVal hfind =>
      simpa_require_family_tail using compile_require_family_clauses_then_setStorage_literal_semantics
          fields fieldName slot init clauses writeVal hfind
  | iteEqSetStorageLiterals fieldName slot n m thenVal elseVal hfind =>
      simpa_require_family_tail using compile_require_family_clauses_then_ite_eq_setStorage_literals_semantics
          fields fieldName slot init clauses n m thenVal elseVal hfind
  | iteEqSetStorageThenReturnLiteral fieldName slot n m thenVal elseVal hfind =>
      simpa_require_family_tail using compile_require_family_clauses_then_ite_eq_setStorage_then_return_literal_semantics
          fields fieldName slot init clauses n m thenVal elseVal hfind
  | iteEqReturnThenSetStorageLiteral fieldName slot n m thenVal elseVal hfind =>
      simpa_require_family_tail using compile_require_family_clauses_then_ite_eq_return_then_setStorage_literal_semantics
          fields fieldName slot init clauses n m thenVal elseVal hfind
  | iteEqReturnLiterals n m thenVal elseVal =>
      simpa_require_family_tail using compile_require_family_clauses_then_ite_eq_return_literals_semantics
          fields init clauses n m thenVal elseVal
  | iteEqThenIteEqReturnLiterals n m p q thenVal elseVal outerElseVal =>
      simpa_require_family_tail using compile_require_family_clauses_then_ite_eq_then_ite_eq_return_literals_semantics
          fields init clauses n m p q thenVal elseVal outerElseVal
  | iteEqThenIteEqSetStorageLiteralsThenReturnLiteral
      fieldName slot n m p q thenVal elseVal outerElseVal hfind =>
      simpa_require_family_tail using
          compile_require_family_clauses_then_ite_eq_then_ite_eq_setStorage_literals_then_return_literal_semantics
            fields fieldName slot init clauses n m p q thenVal elseVal outerElseVal hfind
  | iteEqThenIteEqReturnLiteralsThenSetStorageLiteral
      fieldName slot n m p q thenVal elseVal outerElseVal hfind =>
      simpa_require_family_tail using
          compile_require_family_clauses_then_ite_eq_then_ite_eq_return_literals_then_setStorage_literal_semantics
            fields fieldName slot init clauses n m p q thenVal elseVal outerElseVal hfind
  | iteEqThenIteEqReturnLiteralsThenSetStorageLiteralThenReturnLiteral
      fieldName slot n m p q thenVal elseVal outerElseWriteVal outerElseRetVal hfind =>
      simpa_require_family_tail using
          compile_require_family_clauses_then_ite_eq_then_ite_eq_return_literals_then_setStorage_literal_then_return_literal_semantics
            fields fieldName slot init clauses n m p q thenVal elseVal outerElseWriteVal outerElseRetVal hfind
  | iteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral
      fieldName slot n m p q thenVal elseVal outerElseVal hfind =>
      simpa_require_family_tail using
          compile_require_family_clauses_then_ite_eq_then_ite_eq_setStorage_literals_then_setStorage_literal_semantics
            fields fieldName slot init clauses n m p q thenVal elseVal outerElseVal hfind
  | iteEqThenIteEqSetStorageThenReturnLiteralThenReturnLiteral
      fieldName slot n m p q thenVal elseVal outerElseVal hfind =>
      simpa_require_family_tail using
          compile_require_family_clauses_then_ite_eq_then_ite_eq_setStorage_then_return_literal_then_return_literal_semantics
            fields fieldName slot init clauses n m p q thenVal elseVal outerElseVal hfind
  | iteEqThenIteEqSetStorageThenReturnLiteralThenSetStorageLiteral
      fieldName slot n m p q thenVal elseVal outerElseVal hfind =>
      simpa_require_family_tail using
          compile_require_family_clauses_then_ite_eq_then_ite_eq_setStorage_then_return_literal_then_setStorage_literal_semantics
            fields fieldName slot init clauses n m p q thenVal elseVal outerElseVal hfind
  | iteEqThenIteEqReturnThenSetStorageLiteralThenReturnLiteral
      fieldName slot n m p q thenVal elseVal outerElseVal hfind =>
      simpa_require_family_tail using
          compile_require_family_clauses_then_ite_eq_then_ite_eq_return_then_setStorage_literal_then_return_literal_semantics
            fields fieldName slot init clauses n m p q thenVal elseVal outerElseVal hfind
  | iteEqThenIteEqReturnThenSetStorageLiteralThenSetStorageLiteral
      fieldName slot n m p q thenVal elseVal outerElseVal hfind =>
      simpa_require_family_tail using
          compile_require_family_clauses_then_ite_eq_then_ite_eq_return_then_setStorage_literal_then_setStorage_literal_semantics
            fields fieldName slot init clauses n m p q thenVal elseVal outerElseVal hfind
  | returnLiteral retVal =>
      simpa_require_family_tail using compile_require_family_clauses_then_return_literal_semantics fields init clauses retVal
  | letReturnLocalLiteral tmp retVal =>
      simpa_require_family_tail using compile_require_family_clauses_then_let_return_local_literal_semantics
          fields tmp init clauses retVal
  | letSetStorageLocalLiteral fieldName tmp slot n hfind =>
      simpa_require_family_tail using compile_require_family_clauses_then_let_setStorage_local_literal_semantics
          fields fieldName tmp slot init clauses n hfind
  | letAssignSetStorageLocalLiteral fieldName tmp slot n m hfind =>
      simpa_require_family_tail using compile_require_family_clauses_then_let_assign_setStorage_local_literal_semantics
          fields fieldName tmp slot init clauses n m hfind
  | letAssignAddSetStorageLocalLiteral fieldName tmp slot n m hfind =>
      simpa_require_family_tail using compile_require_family_clauses_then_let_assign_add_setStorage_local_literal_semantics
          fields fieldName tmp slot init clauses n m hfind
  | letAssignSubSetStorageLocalLiteral fieldName tmp slot n m hfind =>
      simpa_require_family_tail using compile_require_family_clauses_then_let_assign_sub_setStorage_local_literal_semantics
          fields fieldName tmp slot init clauses n m hfind
  | letAssignMulSetStorageLocalLiteral fieldName tmp slot n m hfind =>
      simpa_require_family_tail using compile_require_family_clauses_then_let_assign_mul_setStorage_local_literal_semantics
          fields fieldName tmp slot init clauses n m hfind
  | letStorageSetStorageAddLocalStop fieldName tmp slot m hfind =>
      simpa_require_family_tail using compile_require_family_clauses_then_let_storage_setStorage_add_local_stop_semantics
          fields fieldName tmp slot init clauses m hfind
  | letStorageSetStorageSubLocalStop fieldName tmp slot m hfind =>
      simpa_require_family_tail using compile_require_family_clauses_then_let_storage_setStorage_sub_local_stop_semantics
          fields fieldName tmp slot init clauses m hfind
  | letStorageReturnLocal fieldName tmp slot hfind =>
      simpa_require_family_tail using compile_require_family_clauses_then_let_storage_return_local_semantics
          fields fieldName tmp slot init clauses hfind
  | returnStorage fieldName slot hfind =>
      simpa_require_family_tail using compile_require_family_clauses_then_return_storage_semantics
          fields fieldName slot init clauses hfind
  | returnStorageAddr fieldName slot hfind =>
      simpa_require_family_tail using compile_require_family_clauses_then_return_storage_addr_semantics
          fields fieldName slot init clauses hfind
  | requireCallerEqStorageAddrSetStorageAddStop ownerField countField msg ownerSlot countSlot n hOwner hCount =>
      simpa_require_family_tail using compile_require_family_clauses_then_require_caller_eq_storage_addr_setStorage_add_stop_semantics
          fields ownerField countField ownerSlot countSlot init clauses n msg hOwner hCount
  | requireCallerEqStorageAddrSetStorageSubStop ownerField countField msg ownerSlot countSlot n hOwner hCount =>
      simpa_require_family_tail using compile_require_family_clauses_then_require_caller_eq_storage_addr_setStorage_sub_stop_semantics
          fields ownerField countField ownerSlot countSlot init clauses n msg hOwner hCount
  | returnMappingCaller fieldName slot hSlot =>
      simpa_require_family_tail using compile_require_family_clauses_then_return_mapping_caller_semantics
          fields fieldName slot init clauses hSlot
  | letStorageAddrReturnLocal fieldName tmp slot hfind =>
      simpa_require_family_tail using compile_require_family_clauses_then_let_storage_addr_return_local_semantics
          fields fieldName tmp slot init clauses hfind
  | letMappingParamReturnLocal fieldName paramName tmp slot hSlot =>
      simpa_require_family_tail using compile_require_family_clauses_then_let_mapping_param_return_local_semantics
          fields fieldName paramName tmp slot init clauses hSlot
  | letMapping2ParamsReturnLocal fieldName p1 p2 tmp slot hSlot hp =>
      simpa_require_family_tail using compile_require_family_clauses_then_let_mapping2_params_return_local_semantics
          fields fieldName p1 p2 tmp slot init clauses hSlot hp
  | letCallerSetMapping2Stop fieldName senderVar p1 p2 slot hSlot h1 h2 h3 h4 h5 h6 =>
      simpa_require_family_tail using compile_require_family_clauses_then_let_caller_setMapping2_stop_semantics
          fields fieldName senderVar p1 p2 slot init clauses hSlot h1 h2 h3 h4 h5 h6
  | letMappingUintParamReturnLocal fieldName paramName tmp slot hSlot =>
      simpa_require_family_tail using compile_require_family_clauses_then_let_mappingUint_param_return_local_semantics
          fields fieldName paramName tmp slot init clauses hSlot
  | setMappingUintParamsStop fieldName p1 p2 slot hSlot hp =>
      simpa_require_family_tail using compile_require_family_clauses_then_setMappingUint_params_stop_semantics
          fields fieldName p1 p2 slot init clauses hSlot hp
  -- Morpho admin tails
  | letCallerLetStorageAddrReqEqReqNeqSetStorageAddrParamStop
      ownerField senderVar ownerVar paramName msg1 msg2 ownerSlot hOwner hne_sv_p hne_ov_p hne_ov_sv =>
      simp [execCompiledRequireFamilyClausesThenTail, execSourceRequireFamilyClausesThenTail,
        compile_require_literal_guard_family_clauses_semantics,
        compile_letCaller_letStorageAddr_reqEq_reqNeq_setStorageAddr_param_stop_semantics
          fields ownerField senderVar ownerVar paramName msg1 msg2 ownerSlot _ hOwner hne_sv_p hne_ov_p hne_ov_sv]
  | letCallerLetStorageAddrReqEqLetMappingReqEqLitSetMappingStop
      ownerField mappingField senderVar ownerVar currentVar keyParam ownerSlot mappingSlot writeVal msg1 msg2
      hOwner hMapping hne_sv_kp hne_ov_kp hne_ov_sv hne_cv_kp =>
      simp [execCompiledRequireFamilyClausesThenTail, execSourceRequireFamilyClausesThenTail,
        compile_require_literal_guard_family_clauses_semantics,
        compile_letCaller_letStorageAddr_reqEq_letMapping_reqEqLit_setMapping_stop_semantics
          fields ownerField mappingField senderVar ownerVar currentVar keyParam ownerSlot mappingSlot writeVal _
          msg1 msg2 hOwner hMapping hne_sv_kp hne_ov_kp hne_ov_sv hne_cv_kp]
  | letCallerLetStorageAddrReqEqLetMappingUintReqEqLitReqLtSetMappingUintStop
      ownerField mappingField senderVar ownerVar currentVar keyParam ownerSlot mappingSlot bound writeVal
      msg1 msg2 msg3 hOwner hMapping hne_sv_kp hne_ov_kp hne_ov_sv hne_cv_kp =>
      simp [execCompiledRequireFamilyClausesThenTail, execSourceRequireFamilyClausesThenTail,
        compile_require_literal_guard_family_clauses_semantics,
        compile_letCaller_letStorageAddr_reqEq_letMappingUint_reqEqLit_reqLt_setMappingUint_stop_semantics
          fields ownerField mappingField senderVar ownerVar currentVar keyParam ownerSlot mappingSlot bound writeVal _
          msg1 msg2 msg3 hOwner hMapping hne_sv_kp hne_ov_kp hne_ov_sv hne_cv_kp]
  | letCallerLetMapping2IteParamReqSetMapping2Stop
      mappingField senderVar currentVar authParam boolParam msg1 msg2 mappingSlot
      hMapping hne_sv_bp hne_sv_ap hne_cv_bp hne_cv_ap hne_cv_sv hne_bp_ap =>
      simp [execCompiledRequireFamilyClausesThenTail, execSourceRequireFamilyClausesThenTail,
        compile_require_literal_guard_family_clauses_semantics,
        compile_letCaller_letMapping2_ite_param_req_setMapping2_stop_semantics
          fields mappingField senderVar currentVar authParam boolParam mappingSlot _
          msg1 msg2 hMapping hne_sv_bp hne_sv_ap hne_cv_bp hne_cv_ap hne_cv_sv hne_bp_ap]

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
            simp [compile_require_family_clauses_tail_programs_semantics]
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
  | requireClausesThenIteEqThenIteEqReturnLiteralsThenSetStorageLiteralThenReturnLiteral
      (clauses : List RequireLiteralGuardFamilyClause)
      (fieldName : String) (slot : Nat)
      (n m p q thenVal elseVal outerElseWriteVal outerElseRetVal : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | requireClausesThenIteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral
      (clauses : List RequireLiteralGuardFamilyClause)
      (fieldName : String) (slot : Nat)
      (n m p q thenVal elseVal outerElseVal : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | requireClausesThenIteEqThenIteEqSetStorageThenReturnLiteralThenReturnLiteral
      (clauses : List RequireLiteralGuardFamilyClause)
      (fieldName : String) (slot : Nat)
      (n m p q thenVal elseVal outerElseVal : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | requireClausesThenIteEqThenIteEqSetStorageThenReturnLiteralThenSetStorageLiteral
      (clauses : List RequireLiteralGuardFamilyClause)
      (fieldName : String) (slot : Nat)
      (n m p q thenVal elseVal outerElseVal : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | requireClausesThenIteEqThenIteEqReturnThenSetStorageLiteralThenReturnLiteral
      (clauses : List RequireLiteralGuardFamilyClause)
      (fieldName : String) (slot : Nat)
      (n m p q thenVal elseVal outerElseVal : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | requireClausesThenIteEqThenIteEqReturnThenSetStorageLiteralThenSetStorageLiteral
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
  | requireClausesThenLetStorageSetStorageAddLocalStop
      (clauses : List RequireLiteralGuardFamilyClause)
      (fieldName tmp : String) (slot : Nat) (m : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | requireClausesThenLetStorageSetStorageSubLocalStop
      (clauses : List RequireLiteralGuardFamilyClause)
      (fieldName tmp : String) (slot : Nat) (m : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | requireClausesThenLetStorageReturnLocal
      (clauses : List RequireLiteralGuardFamilyClause)
      (fieldName tmp : String) (slot : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | requireClausesThenReturnStorage
      (clauses : List RequireLiteralGuardFamilyClause)
      (fieldName : String) (slot : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | requireClausesThenReturnStorageAddr
      (clauses : List RequireLiteralGuardFamilyClause)
      (fieldName : String) (slot : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.address }, slot))
  | requireClausesThenRequireCallerEqStorageAddrSetStorageAddStop
      (clauses : List RequireLiteralGuardFamilyClause)
      (ownerField countField msg : String) (ownerSlot countSlot : Nat) (n : Nat)
      (hOwner : findFieldWithResolvedSlot fields ownerField =
        some ({ name := ownerField, ty := FieldType.address }, ownerSlot))
      (hCount : findFieldWithResolvedSlot fields countField =
        some ({ name := countField, ty := FieldType.uint256 }, countSlot))
  | requireClausesThenRequireCallerEqStorageAddrSetStorageSubStop
      (clauses : List RequireLiteralGuardFamilyClause)
      (ownerField countField msg : String) (ownerSlot countSlot : Nat) (n : Nat)
      (hOwner : findFieldWithResolvedSlot fields ownerField =
        some ({ name := ownerField, ty := FieldType.address }, ownerSlot))
      (hCount : findFieldWithResolvedSlot fields countField =
        some ({ name := countField, ty := FieldType.uint256 }, countSlot))
  | requireClausesThenReturnMappingCaller
      (clauses : List RequireLiteralGuardFamilyClause)
      (fieldName : String) (slot : Nat)
      (hSlot : findFieldSlot fields fieldName = some slot)
  | requireClausesThenLetStorageAddrReturnLocal
      (clauses : List RequireLiteralGuardFamilyClause)
      (fieldName tmp : String) (slot : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.address }, slot))
  | requireClausesThenLetMappingParamReturnLocal
      (clauses : List RequireLiteralGuardFamilyClause)
      (fieldName paramName tmp : String) (slot : Nat)
      (hSlot : findFieldSlot fields fieldName = some slot)
  | requireClausesThenLetMapping2ParamsReturnLocal
      (clauses : List RequireLiteralGuardFamilyClause)
      (fieldName p1 p2 tmp : String) (slot : Nat)
      (hSlot : findFieldSlot fields fieldName = some slot)
      (hp : p1 ≠ p2)
  | requireClausesThenLetCallerSetMapping2Stop
      (clauses : List RequireLiteralGuardFamilyClause)
      (fieldName senderVar p1 p2 : String) (slot : Nat)
      (hSlot : findFieldSlot fields fieldName = some slot)
      (h1 : senderVar ≠ p2) (h2 : senderVar ≠ p1) (h3 : p2 ≠ p1)
      (h4 : p1 ≠ p2) (h5 : p1 ≠ senderVar) (h6 : p2 ≠ senderVar)
  | requireClausesThenLetMappingUintParamReturnLocal
      (clauses : List RequireLiteralGuardFamilyClause)
      (fieldName paramName tmp : String) (slot : Nat)
      (hSlot : findFieldSlot fields fieldName = some slot)
  | requireClausesThenSetMappingUintParamsStop
      (clauses : List RequireLiteralGuardFamilyClause)
      (fieldName p1 p2 : String) (slot : Nat)
      (hSlot : findFieldSlot fields fieldName = some slot)
      (hp : p1 ≠ p2)
  -- Morpho Blue admin function fragments (empty clause prefix)
  | letCallerLetStorageAddrReqEqReqNeqSetStorageAddrParamStop
      (ownerField senderVar ownerVar paramName msg1 msg2 : String) (ownerSlot : Nat)
      (hOwner : findFieldWithResolvedSlot fields ownerField =
        some ({ name := ownerField, ty := FieldType.address }, ownerSlot))
      (hne_sv_p : senderVar ≠ paramName)
      (hne_ov_p : ownerVar ≠ paramName)
      (hne_ov_sv : ownerVar ≠ senderVar)
  | letCallerLetStorageAddrReqEqLetMappingReqEqLitSetMappingStop
      (ownerField mappingField senderVar ownerVar currentVar keyParam : String)
      (ownerSlot mappingSlot : Nat) (writeVal : Nat) (msg1 msg2 : String)
      (hOwner : findFieldWithResolvedSlot fields ownerField =
        some ({ name := ownerField, ty := FieldType.address }, ownerSlot))
      (hMapping : findFieldSlot fields mappingField = some mappingSlot)
      (hne_sv_kp : senderVar ≠ keyParam)
      (hne_ov_kp : ownerVar ≠ keyParam)
      (hne_ov_sv : ownerVar ≠ senderVar)
      (hne_cv_kp : currentVar ≠ keyParam)
  | letCallerLetStorageAddrReqEqLetMappingUintReqEqLitReqLtSetMappingUintStop
      (ownerField mappingField senderVar ownerVar currentVar keyParam : String)
      (ownerSlot mappingSlot : Nat) (bound writeVal : Nat) (msg1 msg2 msg3 : String)
      (hOwner : findFieldWithResolvedSlot fields ownerField =
        some ({ name := ownerField, ty := FieldType.address }, ownerSlot))
      (hMapping : findFieldSlot fields mappingField = some mappingSlot)
      (hne_sv_kp : senderVar ≠ keyParam)
      (hne_ov_kp : ownerVar ≠ keyParam)
      (hne_ov_sv : ownerVar ≠ senderVar)
      (hne_cv_kp : currentVar ≠ keyParam)
  | letCallerLetMapping2IteParamReqSetMapping2Stop
      (mappingField senderVar currentVar authParam boolParam msg1 msg2 : String) (mappingSlot : Nat)
      (hMapping : findFieldSlot fields mappingField = some mappingSlot)
      (hne_sv_bp : senderVar ≠ boolParam)
      (hne_sv_ap : senderVar ≠ authParam)
      (hne_cv_bp : currentVar ≠ boolParam)
      (hne_cv_ap : currentVar ≠ authParam)
      (hne_cv_sv : currentVar ≠ senderVar)
      (hne_bp_ap : boolParam ≠ authParam)

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
  | .requireClausesThenIteEqThenIteEqReturnLiteralsThenSetStorageLiteralThenReturnLiteral
      clauses fieldName slot n m p q thenVal elseVal outerElseWriteVal outerElseRetVal hfind =>
      { clauses := clauses
        tail := .iteEqThenIteEqReturnLiteralsThenSetStorageLiteralThenReturnLiteral
          fieldName slot n m p q thenVal elseVal outerElseWriteVal outerElseRetVal hfind }
  | .requireClausesThenIteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral
      clauses fieldName slot n m p q thenVal elseVal outerElseVal hfind =>
      { clauses := clauses
        tail := .iteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral
          fieldName slot n m p q thenVal elseVal outerElseVal hfind }
  | .requireClausesThenIteEqThenIteEqSetStorageThenReturnLiteralThenReturnLiteral
      clauses fieldName slot n m p q thenVal elseVal outerElseVal hfind =>
      { clauses := clauses
        tail := .iteEqThenIteEqSetStorageThenReturnLiteralThenReturnLiteral
          fieldName slot n m p q thenVal elseVal outerElseVal hfind }
  | .requireClausesThenIteEqThenIteEqSetStorageThenReturnLiteralThenSetStorageLiteral
      clauses fieldName slot n m p q thenVal elseVal outerElseVal hfind =>
      { clauses := clauses
        tail := .iteEqThenIteEqSetStorageThenReturnLiteralThenSetStorageLiteral
          fieldName slot n m p q thenVal elseVal outerElseVal hfind }
  | .requireClausesThenIteEqThenIteEqReturnThenSetStorageLiteralThenReturnLiteral
      clauses fieldName slot n m p q thenVal elseVal outerElseVal hfind =>
      { clauses := clauses
        tail := .iteEqThenIteEqReturnThenSetStorageLiteralThenReturnLiteral
          fieldName slot n m p q thenVal elseVal outerElseVal hfind }
  | .requireClausesThenIteEqThenIteEqReturnThenSetStorageLiteralThenSetStorageLiteral
      clauses fieldName slot n m p q thenVal elseVal outerElseVal hfind =>
      { clauses := clauses
        tail := .iteEqThenIteEqReturnThenSetStorageLiteralThenSetStorageLiteral
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
  | .requireClausesThenLetStorageSetStorageAddLocalStop clauses fieldName tmp slot m hfind =>
      { clauses := clauses
        tail := .letStorageSetStorageAddLocalStop fieldName tmp slot m hfind }
  | .requireClausesThenLetStorageSetStorageSubLocalStop clauses fieldName tmp slot m hfind =>
      { clauses := clauses
        tail := .letStorageSetStorageSubLocalStop fieldName tmp slot m hfind }
  | .requireClausesThenLetStorageReturnLocal clauses fieldName tmp slot hfind =>
      { clauses := clauses
        tail := .letStorageReturnLocal fieldName tmp slot hfind }
  | .requireClausesThenReturnStorage clauses fieldName slot hfind =>
      { clauses := clauses
        tail := .returnStorage fieldName slot hfind }
  | .requireClausesThenReturnStorageAddr clauses fieldName slot hfind =>
      { clauses := clauses
        tail := .returnStorageAddr fieldName slot hfind }
  | .requireClausesThenRequireCallerEqStorageAddrSetStorageAddStop
      clauses ownerField countField msg ownerSlot countSlot n hOwner hCount =>
      { clauses := clauses
        tail := .requireCallerEqStorageAddrSetStorageAddStop
          ownerField countField msg ownerSlot countSlot n hOwner hCount }
  | .requireClausesThenRequireCallerEqStorageAddrSetStorageSubStop
      clauses ownerField countField msg ownerSlot countSlot n hOwner hCount =>
      { clauses := clauses
        tail := .requireCallerEqStorageAddrSetStorageSubStop
          ownerField countField msg ownerSlot countSlot n hOwner hCount }
  | .requireClausesThenReturnMappingCaller clauses fieldName slot hSlot =>
      { clauses := clauses
        tail := .returnMappingCaller fieldName slot hSlot }
  | .requireClausesThenLetStorageAddrReturnLocal clauses fieldName tmp slot hfind =>
      { clauses := clauses
        tail := .letStorageAddrReturnLocal fieldName tmp slot hfind }
  | .requireClausesThenLetMappingParamReturnLocal clauses fieldName paramName tmp slot hSlot =>
      { clauses := clauses
        tail := .letMappingParamReturnLocal fieldName paramName tmp slot hSlot }
  | .requireClausesThenLetMapping2ParamsReturnLocal clauses fieldName p1 p2 tmp slot hSlot hp =>
      { clauses := clauses
        tail := .letMapping2ParamsReturnLocal fieldName p1 p2 tmp slot hSlot hp }
  | .requireClausesThenLetCallerSetMapping2Stop clauses fieldName senderVar p1 p2 slot hSlot h1 h2 h3 h4 h5 h6 =>
      { clauses := clauses
        tail := .letCallerSetMapping2Stop fieldName senderVar p1 p2 slot hSlot h1 h2 h3 h4 h5 h6 }
  | .requireClausesThenLetMappingUintParamReturnLocal clauses fieldName paramName tmp slot hSlot =>
      { clauses := clauses
        tail := .letMappingUintParamReturnLocal fieldName paramName tmp slot hSlot }
  | .requireClausesThenSetMappingUintParamsStop clauses fieldName p1 p2 slot hSlot hp =>
      { clauses := clauses
        tail := .setMappingUintParamsStop fieldName p1 p2 slot hSlot hp }
  -- Morpho admin fragments: empty clause list, tail encodes the full body
  | .letCallerLetStorageAddrReqEqReqNeqSetStorageAddrParamStop
      ownerField senderVar ownerVar paramName msg1 msg2 ownerSlot hOwner hne_sv_p hne_ov_p hne_ov_sv =>
      { clauses := []
        tail := .letCallerLetStorageAddrReqEqReqNeqSetStorageAddrParamStop
          ownerField senderVar ownerVar paramName msg1 msg2 ownerSlot hOwner hne_sv_p hne_ov_p hne_ov_sv }
  | .letCallerLetStorageAddrReqEqLetMappingReqEqLitSetMappingStop
      ownerField mappingField senderVar ownerVar currentVar keyParam ownerSlot mappingSlot writeVal msg1 msg2
      hOwner hMapping hne_sv_kp hne_ov_kp hne_ov_sv hne_cv_kp =>
      { clauses := []
        tail := .letCallerLetStorageAddrReqEqLetMappingReqEqLitSetMappingStop
          ownerField mappingField senderVar ownerVar currentVar keyParam ownerSlot mappingSlot writeVal msg1 msg2
          hOwner hMapping hne_sv_kp hne_ov_kp hne_ov_sv hne_cv_kp }
  | .letCallerLetStorageAddrReqEqLetMappingUintReqEqLitReqLtSetMappingUintStop
      ownerField mappingField senderVar ownerVar currentVar keyParam ownerSlot mappingSlot bound writeVal
      msg1 msg2 msg3 hOwner hMapping hne_sv_kp hne_ov_kp hne_ov_sv hne_cv_kp =>
      { clauses := []
        tail := .letCallerLetStorageAddrReqEqLetMappingUintReqEqLitReqLtSetMappingUintStop
          ownerField mappingField senderVar ownerVar currentVar keyParam ownerSlot mappingSlot bound writeVal
          msg1 msg2 msg3 hOwner hMapping hne_sv_kp hne_ov_kp hne_ov_sv hne_cv_kp }
  | .letCallerLetMapping2IteParamReqSetMapping2Stop
      mappingField senderVar currentVar authParam boolParam msg1 msg2 mappingSlot
      hMapping hne_sv_bp hne_sv_ap hne_cv_bp hne_cv_ap hne_cv_sv hne_bp_ap =>
      { clauses := []
        tail := .letCallerLetMapping2IteParamReqSetMapping2Stop
          mappingField senderVar currentVar authParam boolParam msg1 msg2 mappingSlot
          hMapping hne_sv_bp hne_sv_ap hne_cv_bp hne_cv_ap hne_cv_sv hne_bp_ap }

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
  | .iteEqThenIteEqReturnLiteralsThenSetStorageLiteralThenReturnLiteral
      fieldName _ n m p q thenVal elseVal outerElseWriteVal outerElseRetVal _ =>
      [Stmt.ite (Expr.eq (Expr.literal n) (Expr.literal m))
          [Stmt.ite (Expr.eq (Expr.literal p) (Expr.literal q))
            [Stmt.return (Expr.literal thenVal)]
            [Stmt.return (Expr.literal elseVal)]]
          [Stmt.setStorage fieldName (Expr.literal outerElseWriteVal),
           Stmt.return (Expr.literal outerElseRetVal)]]
  | .iteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral
      fieldName _ n m p q thenVal elseVal outerElseVal _ =>
      [Stmt.ite (Expr.eq (Expr.literal n) (Expr.literal m))
          [Stmt.ite (Expr.eq (Expr.literal p) (Expr.literal q))
            [Stmt.setStorage fieldName (Expr.literal thenVal)]
            [Stmt.setStorage fieldName (Expr.literal elseVal)]]
          [Stmt.setStorage fieldName (Expr.literal outerElseVal)]]
  | .iteEqThenIteEqSetStorageThenReturnLiteralThenReturnLiteral
      fieldName _ n m p q thenVal elseVal outerElseVal _ =>
      [Stmt.ite (Expr.eq (Expr.literal n) (Expr.literal m))
          [Stmt.ite (Expr.eq (Expr.literal p) (Expr.literal q))
            [Stmt.setStorage fieldName (Expr.literal thenVal)]
            [Stmt.return (Expr.literal elseVal)]]
          [Stmt.return (Expr.literal outerElseVal)]]
  | .iteEqThenIteEqSetStorageThenReturnLiteralThenSetStorageLiteral
      fieldName _ n m p q thenVal elseVal outerElseVal _ =>
      [Stmt.ite (Expr.eq (Expr.literal n) (Expr.literal m))
          [Stmt.ite (Expr.eq (Expr.literal p) (Expr.literal q))
            [Stmt.setStorage fieldName (Expr.literal thenVal)]
            [Stmt.return (Expr.literal elseVal)]]
          [Stmt.setStorage fieldName (Expr.literal outerElseVal)]]
  | .iteEqThenIteEqReturnThenSetStorageLiteralThenReturnLiteral
      fieldName _ n m p q thenVal elseVal outerElseVal _ =>
      [Stmt.ite (Expr.eq (Expr.literal n) (Expr.literal m))
          [Stmt.ite (Expr.eq (Expr.literal p) (Expr.literal q))
            [Stmt.return (Expr.literal thenVal)]
            [Stmt.setStorage fieldName (Expr.literal elseVal)]]
          [Stmt.return (Expr.literal outerElseVal)]]
  | .iteEqThenIteEqReturnThenSetStorageLiteralThenSetStorageLiteral
      fieldName _ n m p q thenVal elseVal outerElseVal _ =>
      [Stmt.ite (Expr.eq (Expr.literal n) (Expr.literal m))
          [Stmt.ite (Expr.eq (Expr.literal p) (Expr.literal q))
            [Stmt.return (Expr.literal thenVal)]
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
  | .letStorageSetStorageAddLocalStop fieldName tmp _ m _ =>
      [ Stmt.letVar tmp (Expr.storage fieldName)
      , Stmt.setStorage fieldName (Expr.add (Expr.localVar tmp) (Expr.literal m))
      , Stmt.stop
      ]
  | .letStorageSetStorageSubLocalStop fieldName tmp _ m _ =>
      [ Stmt.letVar tmp (Expr.storage fieldName)
      , Stmt.setStorage fieldName (Expr.sub (Expr.localVar tmp) (Expr.literal m))
      , Stmt.stop
      ]
  | .letStorageReturnLocal fieldName tmp _ _ =>
      [ Stmt.letVar tmp (Expr.storage fieldName)
      , Stmt.return (Expr.localVar tmp)
      ]
  | .returnStorage fieldName _ _ =>
      [Stmt.return (Expr.storage fieldName)]
  | .returnStorageAddr fieldName _ _ =>
      [Stmt.return (Expr.storage fieldName)]
  | .requireCallerEqStorageAddrSetStorageAddStop ownerField countField msg _ _ n _ _ =>
      [ Stmt.require (Expr.eq Expr.caller (Expr.storage ownerField)) msg
      , Stmt.setStorage countField (Expr.add (Expr.storage countField) (Expr.literal n))
      , Stmt.stop ]
  | .requireCallerEqStorageAddrSetStorageSubStop ownerField countField msg _ _ n _ _ =>
      [ Stmt.require (Expr.eq Expr.caller (Expr.storage ownerField)) msg
      , Stmt.setStorage countField (Expr.sub (Expr.storage countField) (Expr.literal n))
      , Stmt.stop ]
  | .returnMappingCaller fieldName _ _ =>
      [Stmt.return (Expr.mapping fieldName Expr.caller)]
  | .letStorageAddrReturnLocal fieldName tmp _ _ =>
      [ Stmt.letVar tmp (Expr.storage fieldName)
      , Stmt.return (Expr.localVar tmp) ]
  | .letMappingParamReturnLocal fieldName paramName tmp _ _ =>
      [ Stmt.letVar tmp (Expr.mapping fieldName (Expr.param paramName))
      , Stmt.return (Expr.localVar tmp) ]
  | .letMapping2ParamsReturnLocal fieldName p1 p2 tmp _ _ _ =>
      [ Stmt.letVar tmp (Expr.mapping2 fieldName (Expr.param p1) (Expr.param p2))
      , Stmt.return (Expr.localVar tmp) ]
  | .letCallerSetMapping2Stop fieldName senderVar p1 p2 _ _ _ _ _ _ _ _ =>
      [ Stmt.letVar senderVar Expr.caller
      , Stmt.setMapping2 fieldName (Expr.localVar senderVar) (Expr.param p1) (Expr.param p2)
      , Stmt.stop ]
  | .letMappingUintParamReturnLocal fieldName paramName tmp _ _ =>
      [ Stmt.letVar tmp (Expr.mappingUint fieldName (Expr.param paramName))
      , Stmt.return (Expr.localVar tmp) ]
  | .setMappingUintParamsStop fieldName p1 p2 _ _ _ =>
      [ Stmt.setMappingUint fieldName (Expr.param p1) (Expr.param p2)
      , Stmt.stop ]
  -- Morpho admin tails
  | .letCallerLetStorageAddrReqEqReqNeqSetStorageAddrParamStop
      ownerField senderVar ownerVar paramName msg1 msg2 _ _ _ _ _ =>
      [ Stmt.letVar senderVar Expr.caller
      , Stmt.letVar ownerVar (Expr.storage ownerField)
      , Stmt.require (Expr.eq (Expr.localVar senderVar) (Expr.localVar ownerVar)) msg1
      , Stmt.require (Expr.logicalNot (Expr.eq (Expr.param paramName) (Expr.localVar ownerVar))) msg2
      , Stmt.setStorage ownerField (Expr.param paramName)
      , Stmt.stop ]
  | .letCallerLetStorageAddrReqEqLetMappingReqEqLitSetMappingStop
      ownerField mappingField senderVar ownerVar currentVar keyParam _ _ writeVal msg1 msg2
      _ _ _ _ _ _ =>
      [ Stmt.letVar senderVar Expr.caller
      , Stmt.letVar ownerVar (Expr.storage ownerField)
      , Stmt.require (Expr.eq (Expr.localVar senderVar) (Expr.localVar ownerVar)) msg1
      , Stmt.letVar currentVar (Expr.mapping mappingField (Expr.param keyParam))
      , Stmt.require (Expr.eq (Expr.localVar currentVar) (Expr.literal 0)) msg2
      , Stmt.setMapping mappingField (Expr.param keyParam) (Expr.literal writeVal)
      , Stmt.stop ]
  | .letCallerLetStorageAddrReqEqLetMappingUintReqEqLitReqLtSetMappingUintStop
      ownerField mappingField senderVar ownerVar currentVar keyParam _ _ bound writeVal msg1 msg2 msg3
      _ _ _ _ _ _ =>
      [ Stmt.letVar senderVar Expr.caller
      , Stmt.letVar ownerVar (Expr.storage ownerField)
      , Stmt.require (Expr.eq (Expr.localVar senderVar) (Expr.localVar ownerVar)) msg1
      , Stmt.letVar currentVar (Expr.mappingUint mappingField (Expr.param keyParam))
      , Stmt.require (Expr.eq (Expr.localVar currentVar) (Expr.literal 0)) msg2
      , Stmt.require (Expr.lt (Expr.param keyParam) (Expr.literal bound)) msg3
      , Stmt.setMappingUint mappingField (Expr.param keyParam) (Expr.literal writeVal)
      , Stmt.stop ]
  | .letCallerLetMapping2IteParamReqSetMapping2Stop
      mappingField senderVar currentVar authParam boolParam msg1 msg2 _ _ _ _ _ _ _ _ =>
      [ Stmt.letVar senderVar Expr.caller
      , Stmt.letVar currentVar (Expr.mapping2 mappingField (Expr.localVar senderVar) (Expr.param authParam))
      , Stmt.ite (Expr.param boolParam)
          [ Stmt.require (Expr.eq (Expr.localVar currentVar) (Expr.literal 0)) msg1
          , Stmt.setMapping2 mappingField (Expr.localVar senderVar) (Expr.param authParam) (Expr.literal 1) ]
          [ Stmt.require (Expr.logicalNot (Expr.eq (Expr.localVar currentVar) (Expr.literal 0))) msg2
          , Stmt.setMapping2 mappingField (Expr.localVar senderVar) (Expr.param authParam) (Expr.literal 0) ]
      , Stmt.stop ]

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

/-- Counter fields used for bridge theorem instantiation. -/
def counterFields : List Field :=
  [{ name := "count", ty := FieldType.uint256 }]

/-- Counter field resolution: `count` maps to slot 0. -/
theorem counterFieldResolution :
    findFieldWithResolvedSlot counterFields "count" =
      some ({ name := "count", ty := FieldType.uint256 }, 0) := by
  rfl

/-- Counter.increment body belongs to the supported statement fragment grammar. -/
theorem counter_increment_supported :
    SupportedStmtList counterFields
      [ Stmt.letVar "current" (Expr.storage "count")
      , Stmt.setStorage "count" (Expr.add (Expr.localVar "current") (Expr.literal 1))
      , Stmt.stop ] := by
  exact ⟨[.requireClausesThenLetStorageSetStorageAddLocalStop
    [] "count" "current" 0 1 counterFieldResolution], rfl⟩

/-- Counter.decrement body belongs to the supported statement fragment grammar. -/
theorem counter_decrement_supported :
    SupportedStmtList counterFields
      [ Stmt.letVar "current" (Expr.storage "count")
      , Stmt.setStorage "count" (Expr.sub (Expr.localVar "current") (Expr.literal 1))
      , Stmt.stop ] := by
  exact ⟨[.requireClausesThenLetStorageSetStorageSubLocalStop
    [] "count" "current" 0 1 counterFieldResolution], rfl⟩

/-- Counter.getCount body belongs to the supported statement fragment grammar. -/
theorem counter_getCount_supported :
    SupportedStmtList counterFields
      [ Stmt.letVar "current" (Expr.storage "count")
      , Stmt.return (Expr.localVar "current") ] := by
  exact ⟨[.requireClausesThenLetStorageReturnLocal
    [] "count" "current" 0 counterFieldResolution], rfl⟩

/-- Counter.increment compilation correctness: compiled and source semantics match
for the increment function body. -/
theorem counter_increment_correctness (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment counterFields),
      supportedStmtFragmentsToStmts fragments =
        [ Stmt.letVar "current" (Expr.storage "count")
        , Stmt.setStorage "count" (Expr.add (Expr.localVar "current") (Expr.literal 1))
        , Stmt.stop ] ∧
      execCompiledSupportedStmtFragments counterFields init fragments =
        execSourceSupportedStmtFragments counterFields init fragments :=
  compile_supported_stmt_list_semantics counterFields init _ counter_increment_supported

/-- Counter.decrement compilation correctness: compiled and source semantics match
for the decrement function body. -/
theorem counter_decrement_correctness (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment counterFields),
      supportedStmtFragmentsToStmts fragments =
        [ Stmt.letVar "current" (Expr.storage "count")
        , Stmt.setStorage "count" (Expr.sub (Expr.localVar "current") (Expr.literal 1))
        , Stmt.stop ] ∧
      execCompiledSupportedStmtFragments counterFields init fragments =
        execSourceSupportedStmtFragments counterFields init fragments :=
  compile_supported_stmt_list_semantics counterFields init _ counter_decrement_supported

/-- Counter.getCount compilation correctness: compiled and source semantics match
for the getCount function body. -/
theorem counter_getCount_correctness (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment counterFields),
      supportedStmtFragmentsToStmts fragments =
        [ Stmt.letVar "current" (Expr.storage "count")
        , Stmt.return (Expr.localVar "current") ] ∧
      execCompiledSupportedStmtFragments counterFields init fragments =
        execSourceSupportedStmtFragments counterFields init fragments :=
  compile_supported_stmt_list_semantics counterFields init _ counter_getCount_supported

-- ============================================================================
-- SimpleStorage fields and correctness theorems
-- ============================================================================

/-- SimpleStorage fields used for bridge theorem instantiation. -/
def simpleStorageFields : List Field :=
  [{ name := "storedData", ty := FieldType.uint256 }]

/-- SimpleStorage field resolution: `storedData` maps to slot 0. -/
theorem simpleStorageFieldResolution :
    findFieldWithResolvedSlot simpleStorageFields "storedData" =
      some ({ name := "storedData", ty := FieldType.uint256 }, 0) := by
  rfl

/-- SimpleStorage.retrieve body belongs to the supported statement fragment grammar. -/
theorem simpleStorage_retrieve_supported :
    SupportedStmtList simpleStorageFields
      [Stmt.return (Expr.storage "storedData")] := by
  exact ⟨[.requireClausesThenReturnStorage
    [] "storedData" 0 simpleStorageFieldResolution], rfl⟩

/-- SimpleStorage.retrieve compilation correctness: compiled and source semantics match. -/
theorem simpleStorage_retrieve_correctness (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment simpleStorageFields),
      supportedStmtFragmentsToStmts fragments =
        [Stmt.return (Expr.storage "storedData")] ∧
      execCompiledSupportedStmtFragments simpleStorageFields init fragments =
        execSourceSupportedStmtFragments simpleStorageFields init fragments :=
  compile_supported_stmt_list_semantics simpleStorageFields init _ simpleStorage_retrieve_supported

-- ============================================================================
-- Owned fields and correctness theorems
-- ============================================================================

/-- Owned fields used for bridge theorem instantiation. -/
def ownedFields : List Field :=
  [{ name := "owner", ty := FieldType.address }]

/-- Owned field resolution: `owner` maps to slot 0. -/
theorem ownedFieldResolution :
    findFieldWithResolvedSlot ownedFields "owner" =
      some ({ name := "owner", ty := FieldType.address }, 0) := by
  rfl

/-- Owned.getOwner body belongs to the supported statement fragment grammar. -/
theorem owned_getOwner_supported :
    SupportedStmtList ownedFields
      [Stmt.return (Expr.storage "owner")] := by
  exact ⟨[.requireClausesThenReturnStorageAddr
    [] "owner" 0 ownedFieldResolution], rfl⟩

/-- Owned.getOwner compilation correctness: compiled and source semantics match. -/
theorem owned_getOwner_correctness (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment ownedFields),
      supportedStmtFragmentsToStmts fragments =
        [Stmt.return (Expr.storage "owner")] ∧
      execCompiledSupportedStmtFragments ownedFields init fragments =
        execSourceSupportedStmtFragments ownedFields init fragments :=
  compile_supported_stmt_list_semantics ownedFields init _ owned_getOwner_supported

-- ============================================================================
-- SafeCounter fields and correctness theorems
-- ============================================================================

/-- SafeCounter fields used for bridge theorem instantiation. -/
def safeCounterFields : List Field :=
  [{ name := "count", ty := FieldType.uint256 }]

/-- SafeCounter field resolution: `count` maps to slot 0. -/
theorem safeCounterFieldResolution :
    findFieldWithResolvedSlot safeCounterFields "count" =
      some ({ name := "count", ty := FieldType.uint256 }, 0) := by
  rfl

/-- SafeCounter.getCount body belongs to the supported statement fragment grammar. -/
theorem safeCounter_getCount_supported :
    SupportedStmtList safeCounterFields
      [Stmt.return (Expr.storage "count")] := by
  exact ⟨[.requireClausesThenReturnStorage
    [] "count" 0 safeCounterFieldResolution], rfl⟩

/-- SafeCounter.getCount compilation correctness: compiled and source semantics match. -/
theorem safeCounter_getCount_correctness (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment safeCounterFields),
      supportedStmtFragmentsToStmts fragments =
        [Stmt.return (Expr.storage "count")] ∧
      execCompiledSupportedStmtFragments safeCounterFields init fragments =
        execSourceSupportedStmtFragments safeCounterFields init fragments :=
  compile_supported_stmt_list_semantics safeCounterFields init _ safeCounter_getCount_supported

-- ============================================================================
-- OwnedCounter fields and correctness theorems
-- ============================================================================

/-- OwnedCounter fields used for bridge theorem instantiation. -/
def ownedCounterFields : List Field :=
  [{ name := "count", ty := FieldType.uint256 },
   { name := "owner", ty := FieldType.address }]

/-- OwnedCounter field resolution: `count` maps to slot 0. -/
theorem ownedCounterCountFieldResolution :
    findFieldWithResolvedSlot ownedCounterFields "count" =
      some ({ name := "count", ty := FieldType.uint256 }, 0) := by
  rfl

/-- OwnedCounter field resolution: `owner` maps to slot 1. -/
theorem ownedCounterOwnerFieldResolution :
    findFieldWithResolvedSlot ownedCounterFields "owner" =
      some ({ name := "owner", ty := FieldType.address }, 1) := by
  rfl

/-- OwnedCounter.getCount body belongs to the supported statement fragment grammar. -/
theorem ownedCounter_getCount_supported :
    SupportedStmtList ownedCounterFields
      [Stmt.return (Expr.storage "count")] := by
  exact ⟨[.requireClausesThenReturnStorage
    [] "count" 0 ownedCounterCountFieldResolution], rfl⟩

/-- OwnedCounter.getCount compilation correctness. -/
theorem ownedCounter_getCount_correctness (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment ownedCounterFields),
      supportedStmtFragmentsToStmts fragments =
        [Stmt.return (Expr.storage "count")] ∧
      execCompiledSupportedStmtFragments ownedCounterFields init fragments =
        execSourceSupportedStmtFragments ownedCounterFields init fragments :=
  compile_supported_stmt_list_semantics ownedCounterFields init _ ownedCounter_getCount_supported

/-- OwnedCounter.getOwner body belongs to the supported statement fragment grammar. -/
theorem ownedCounter_getOwner_supported :
    SupportedStmtList ownedCounterFields
      [Stmt.return (Expr.storage "owner")] := by
  exact ⟨[.requireClausesThenReturnStorageAddr
    [] "owner" 1 ownedCounterOwnerFieldResolution], rfl⟩

/-- OwnedCounter.getOwner compilation correctness. -/
theorem ownedCounter_getOwner_correctness (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment ownedCounterFields),
      supportedStmtFragmentsToStmts fragments =
        [Stmt.return (Expr.storage "owner")] ∧
      execCompiledSupportedStmtFragments ownedCounterFields init fragments =
        execSourceSupportedStmtFragments ownedCounterFields init fragments :=
  compile_supported_stmt_list_semantics ownedCounterFields init _ ownedCounter_getOwner_supported

/-- OwnedCounter.increment body belongs to the supported statement fragment grammar. -/
theorem ownedCounter_increment_supported :
    SupportedStmtList ownedCounterFields
      [ Stmt.require (Expr.eq Expr.caller (Expr.storage "owner")) "Not owner"
      , Stmt.setStorage "count" (Expr.add (Expr.storage "count") (Expr.literal 1))
      , Stmt.stop ] := by
  exact ⟨[.requireClausesThenRequireCallerEqStorageAddrSetStorageAddStop
    [] "owner" "count" "Not owner" 1 0 1
    ownedCounterOwnerFieldResolution ownedCounterCountFieldResolution], rfl⟩

/-- OwnedCounter.increment compilation correctness. -/
theorem ownedCounter_increment_correctness (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment ownedCounterFields),
      supportedStmtFragmentsToStmts fragments =
        [ Stmt.require (Expr.eq Expr.caller (Expr.storage "owner")) "Not owner"
        , Stmt.setStorage "count" (Expr.add (Expr.storage "count") (Expr.literal 1))
        , Stmt.stop ] ∧
      execCompiledSupportedStmtFragments ownedCounterFields init fragments =
        execSourceSupportedStmtFragments ownedCounterFields init fragments :=
  compile_supported_stmt_list_semantics ownedCounterFields init _ ownedCounter_increment_supported

/-- OwnedCounter.decrement body belongs to the supported statement fragment grammar. -/
theorem ownedCounter_decrement_supported :
    SupportedStmtList ownedCounterFields
      [ Stmt.require (Expr.eq Expr.caller (Expr.storage "owner")) "Not owner"
      , Stmt.setStorage "count" (Expr.sub (Expr.storage "count") (Expr.literal 1))
      , Stmt.stop ] := by
  exact ⟨[.requireClausesThenRequireCallerEqStorageAddrSetStorageSubStop
    [] "owner" "count" "Not owner" 1 0 1
    ownedCounterOwnerFieldResolution ownedCounterCountFieldResolution], rfl⟩

/-- OwnedCounter.decrement compilation correctness. -/
theorem ownedCounter_decrement_correctness (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment ownedCounterFields),
      supportedStmtFragmentsToStmts fragments =
        [ Stmt.require (Expr.eq Expr.caller (Expr.storage "owner")) "Not owner"
        , Stmt.setStorage "count" (Expr.sub (Expr.storage "count") (Expr.literal 1))
        , Stmt.stop ] ∧
      execCompiledSupportedStmtFragments ownedCounterFields init fragments =
        execSourceSupportedStmtFragments ownedCounterFields init fragments :=
  compile_supported_stmt_list_semantics ownedCounterFields init _ ownedCounter_decrement_supported

-- ============================================================================
-- Ledger fields and correctness theorems
-- ============================================================================

/-- Ledger fields used for bridge theorem instantiation. -/
def ledgerFields : List Field :=
  [{ name := "balances", ty := FieldType.mappingTyped (.simple .address) }]

/-- Ledger field slot resolution: `balances` maps to slot 0. -/
theorem ledgerBalancesFieldSlot :
    findFieldSlot ledgerFields "balances" = some 0 := by
  rfl

/-- Ledger field resolution: `balances` is a mapping at slot 0. -/
theorem ledgerBalancesFieldResolution :
    findFieldWithResolvedSlot ledgerFields "balances" =
      some ({ name := "balances", ty := FieldType.mappingTyped (.simple .address) }, 0) := by
  rfl

-- ============================================================================
-- SimpleToken fields and correctness theorems
-- ============================================================================

/-- SimpleToken fields used for bridge theorem instantiation. -/
def simpleTokenFields : List Field :=
  [{ name := "owner", ty := FieldType.address },
   { name := "balances", ty := FieldType.mappingTyped (.simple .address) },
   { name := "totalSupply", ty := FieldType.uint256 }]

/-- SimpleToken field resolution: `owner` maps to slot 0. -/
theorem simpleTokenOwnerFieldResolution :
    findFieldWithResolvedSlot simpleTokenFields "owner" =
      some ({ name := "owner", ty := FieldType.address }, 0) := by
  rfl

/-- SimpleToken field slot resolution: `balances` maps to slot 1. -/
theorem simpleTokenBalancesFieldSlot :
    findFieldSlot simpleTokenFields "balances" = some 1 := by
  rfl

/-- SimpleToken field resolution: `balances` is a mapping at slot 1. -/
theorem simpleTokenBalancesFieldResolution :
    findFieldWithResolvedSlot simpleTokenFields "balances" =
      some ({ name := "balances", ty := FieldType.mappingTyped (.simple .address) }, 1) := by
  rfl

/-- SimpleToken field resolution: `totalSupply` maps to slot 2. -/
theorem simpleTokenTotalSupplyFieldResolution :
    findFieldWithResolvedSlot simpleTokenFields "totalSupply" =
      some ({ name := "totalSupply", ty := FieldType.uint256 }, 2) := by
  rfl

/-- SimpleToken.totalSupply body belongs to the supported statement fragment grammar. -/
theorem simpleToken_totalSupply_supported :
    SupportedStmtList simpleTokenFields
      [Stmt.return (Expr.storage "totalSupply")] := by
  exact ⟨[.requireClausesThenReturnStorage
    [] "totalSupply" 2 simpleTokenTotalSupplyFieldResolution], rfl⟩

/-- SimpleToken.totalSupply compilation correctness: compiled and source semantics match. -/
theorem simpleToken_totalSupply_correctness (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment simpleTokenFields),
      supportedStmtFragmentsToStmts fragments =
        [Stmt.return (Expr.storage "totalSupply")] ∧
      execCompiledSupportedStmtFragments simpleTokenFields init fragments =
        execSourceSupportedStmtFragments simpleTokenFields init fragments :=
  compile_supported_stmt_list_semantics simpleTokenFields init _ simpleToken_totalSupply_supported

/-- SimpleToken.owner body belongs to the supported statement fragment grammar. -/
theorem simpleToken_owner_supported :
    SupportedStmtList simpleTokenFields
      [Stmt.return (Expr.storage "owner")] := by
  exact ⟨[.requireClausesThenReturnStorageAddr
    [] "owner" 0 simpleTokenOwnerFieldResolution], rfl⟩

/-- SimpleToken.owner compilation correctness: compiled and source semantics match. -/
theorem simpleToken_owner_correctness (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment simpleTokenFields),
      supportedStmtFragmentsToStmts fragments =
        [Stmt.return (Expr.storage "owner")] ∧
      execCompiledSupportedStmtFragments simpleTokenFields init fragments =
        execSourceSupportedStmtFragments simpleTokenFields init fragments :=
  compile_supported_stmt_list_semantics simpleTokenFields init _ simpleToken_owner_supported

-- ============================================================================
-- ERC20 fields and correctness theorems
-- ============================================================================

/-- ERC20 fields: ownerSlot (address), totalSupplySlot (uint256),
balancesSlot (mapping address→uint256), allowancesSlot (mapping address→address→uint256). -/
def erc20Fields : List Field :=
  [{ name := "ownerSlot", ty := FieldType.address },
   { name := "totalSupplySlot", ty := FieldType.uint256 },
   { name := "balancesSlot", ty := FieldType.mappingTyped (.simple .address) },
   { name := "allowancesSlot", ty := FieldType.mappingTyped (.nested .address .address) }]

/-- ERC20 field resolution: ownerSlot is address at slot 0. -/
theorem erc20OwnerSlotFieldResolution :
    findFieldWithResolvedSlot erc20Fields "ownerSlot" =
      some ({ name := "ownerSlot", ty := FieldType.address }, 0) := by rfl

/-- ERC20 field resolution: totalSupplySlot is uint256 at slot 1. -/
theorem erc20TotalSupplySlotFieldResolution :
    findFieldWithResolvedSlot erc20Fields "totalSupplySlot" =
      some ({ name := "totalSupplySlot", ty := FieldType.uint256 }, 1) := by rfl

/-- ERC20 field slot: balancesSlot at slot 2. -/
theorem erc20BalancesSlotFieldSlot :
    findFieldSlot erc20Fields "balancesSlot" = some 2 := by rfl

/-- ERC20 field slot: allowancesSlot at slot 3. -/
theorem erc20AllowancesSlotFieldSlot :
    findFieldSlot erc20Fields "allowancesSlot" = some 3 := by rfl

-- -- totalSupply() -- --

/-- ERC20.totalSupply body belongs to the supported statement fragment grammar. -/
theorem erc20_totalSupply_supported :
    SupportedStmtList erc20Fields
      [ Stmt.letVar "currentSupply" (Expr.storage "totalSupplySlot")
      , Stmt.return (Expr.localVar "currentSupply") ] := by
  exact ⟨[.requireClausesThenLetStorageReturnLocal
    [] "totalSupplySlot" "currentSupply" 1 erc20TotalSupplySlotFieldResolution], rfl⟩

/-- ERC20.totalSupply compilation correctness. -/
theorem erc20_totalSupply_correctness (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment erc20Fields),
      supportedStmtFragmentsToStmts fragments =
        [ Stmt.letVar "currentSupply" (Expr.storage "totalSupplySlot")
        , Stmt.return (Expr.localVar "currentSupply") ] ∧
      execCompiledSupportedStmtFragments erc20Fields init fragments =
        execSourceSupportedStmtFragments erc20Fields init fragments :=
  compile_supported_stmt_list_semantics erc20Fields init _ erc20_totalSupply_supported

-- -- owner() -- --

/-- ERC20.owner body belongs to the supported statement fragment grammar. -/
theorem erc20_owner_supported :
    SupportedStmtList erc20Fields
      [ Stmt.letVar "currentOwner" (Expr.storage "ownerSlot")
      , Stmt.return (Expr.localVar "currentOwner") ] := by
  exact ⟨[.requireClausesThenLetStorageAddrReturnLocal
    [] "ownerSlot" "currentOwner" 0 erc20OwnerSlotFieldResolution], rfl⟩

/-- ERC20.owner compilation correctness. -/
theorem erc20_owner_correctness (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment erc20Fields),
      supportedStmtFragmentsToStmts fragments =
        [ Stmt.letVar "currentOwner" (Expr.storage "ownerSlot")
        , Stmt.return (Expr.localVar "currentOwner") ] ∧
      execCompiledSupportedStmtFragments erc20Fields init fragments =
        execSourceSupportedStmtFragments erc20Fields init fragments :=
  compile_supported_stmt_list_semantics erc20Fields init _ erc20_owner_supported

-- -- balanceOf(addr) -- --

/-- ERC20.balanceOf body belongs to the supported statement fragment grammar. -/
theorem erc20_balanceOf_supported :
    SupportedStmtList erc20Fields
      [ Stmt.letVar "currentBalance" (Expr.mapping "balancesSlot" (Expr.param "addr"))
      , Stmt.return (Expr.localVar "currentBalance") ] := by
  exact ⟨[.requireClausesThenLetMappingParamReturnLocal
    [] "balancesSlot" "addr" "currentBalance" 2 erc20BalancesSlotFieldSlot], rfl⟩

/-- ERC20.balanceOf compilation correctness. -/
theorem erc20_balanceOf_correctness (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment erc20Fields),
      supportedStmtFragmentsToStmts fragments =
        [ Stmt.letVar "currentBalance" (Expr.mapping "balancesSlot" (Expr.param "addr"))
        , Stmt.return (Expr.localVar "currentBalance") ] ∧
      execCompiledSupportedStmtFragments erc20Fields init fragments =
        execSourceSupportedStmtFragments erc20Fields init fragments :=
  compile_supported_stmt_list_semantics erc20Fields init _ erc20_balanceOf_supported

-- -- allowanceOf(ownerAddr, spender) -- --

/-- ERC20.allowanceOf body belongs to the supported statement fragment grammar. -/
theorem erc20_allowanceOf_supported :
    SupportedStmtList erc20Fields
      [ Stmt.letVar "currentAllowance"
          (Expr.mapping2 "allowancesSlot" (Expr.param "ownerAddr") (Expr.param "spender"))
      , Stmt.return (Expr.localVar "currentAllowance") ] := by
  exact ⟨[.requireClausesThenLetMapping2ParamsReturnLocal
    [] "allowancesSlot" "ownerAddr" "spender" "currentAllowance" 3
    erc20AllowancesSlotFieldSlot (by decide)], rfl⟩

/-- ERC20.allowanceOf compilation correctness. -/
theorem erc20_allowanceOf_correctness (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment erc20Fields),
      supportedStmtFragmentsToStmts fragments =
        [ Stmt.letVar "currentAllowance"
            (Expr.mapping2 "allowancesSlot" (Expr.param "ownerAddr") (Expr.param "spender"))
        , Stmt.return (Expr.localVar "currentAllowance") ] ∧
      execCompiledSupportedStmtFragments erc20Fields init fragments =
        execSourceSupportedStmtFragments erc20Fields init fragments :=
  compile_supported_stmt_list_semantics erc20Fields init _ erc20_allowanceOf_supported

-- -- approve(spender, amount) -- --

/-- ERC20.approve body belongs to the supported statement fragment grammar. -/
theorem erc20_approve_supported :
    SupportedStmtList erc20Fields
      [ Stmt.letVar "sender" Expr.caller
      , Stmt.setMapping2 "allowancesSlot" (Expr.localVar "sender")
          (Expr.param "spender") (Expr.param "amount")
      , Stmt.stop ] := by
  exact ⟨[.requireClausesThenLetCallerSetMapping2Stop
    [] "allowancesSlot" "sender" "spender" "amount" 3
    erc20AllowancesSlotFieldSlot
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)], rfl⟩

/-- ERC20.approve compilation correctness. -/
theorem erc20_approve_correctness (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment erc20Fields),
      supportedStmtFragmentsToStmts fragments =
        [ Stmt.letVar "sender" Expr.caller
        , Stmt.setMapping2 "allowancesSlot" (Expr.localVar "sender")
            (Expr.param "spender") (Expr.param "amount")
        , Stmt.stop ] ∧
      execCompiledSupportedStmtFragments erc20Fields init fragments =
        execSourceSupportedStmtFragments erc20Fields init fragments :=
  compile_supported_stmt_list_semantics erc20Fields init _ erc20_approve_supported

-- ============================================================
-- ERC721 field definitions and bridge theorems
-- ============================================================

/-- ERC721 contract field layout (matching MacroContracts.lean):
ownerSlot (address, slot 0), totalSupplySlot (uint256, slot 1),
nextTokenIdSlot (uint256, slot 2), ownersSlot (uint256→uint256, slot 3),
tokenApprovalsSlot (uint256→uint256, slot 4). -/
def erc721Fields : List Field :=
  [{ name := "ownerSlot", ty := FieldType.address },
   { name := "totalSupplySlot", ty := FieldType.uint256 },
   { name := "nextTokenIdSlot", ty := FieldType.uint256 },
   { name := "ownersSlot", ty := FieldType.mappingTyped (.simple .uint256) },
   { name := "tokenApprovalsSlot", ty := FieldType.mappingTyped (.simple .uint256) }]

/-- ERC721 field slot: tokenApprovalsSlot at slot 4. -/
theorem erc721TokenApprovalsSlotFieldSlot :
    findFieldSlot erc721Fields "tokenApprovalsSlot" = some 4 := by rfl

-- -- getApproved(tokenId) -- --

/-- ERC721.getApproved body belongs to the supported statement fragment grammar. -/
theorem erc721_getApproved_supported :
    SupportedStmtList erc721Fields
      [ Stmt.letVar "approvedWord" (Expr.mappingUint "tokenApprovalsSlot" (Expr.param "tokenId"))
      , Stmt.return (Expr.localVar "approvedWord") ] := by
  exact ⟨[.requireClausesThenLetMappingUintParamReturnLocal
    [] "tokenApprovalsSlot" "tokenId" "approvedWord" 4
    erc721TokenApprovalsSlotFieldSlot], rfl⟩

/-- ERC721.getApproved compilation correctness. -/
theorem erc721_getApproved_correctness (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment erc721Fields),
      supportedStmtFragmentsToStmts fragments =
        [ Stmt.letVar "approvedWord" (Expr.mappingUint "tokenApprovalsSlot" (Expr.param "tokenId"))
        , Stmt.return (Expr.localVar "approvedWord") ] ∧
      execCompiledSupportedStmtFragments erc721Fields init fragments =
        execSourceSupportedStmtFragments erc721Fields init fragments :=
  compile_supported_stmt_list_semantics erc721Fields init _ erc721_getApproved_supported

-- -- approve(approved, tokenId) -- --

/-- ERC721.approve body belongs to the supported statement fragment grammar. -/
theorem erc721_approve_supported :
    SupportedStmtList erc721Fields
      [ Stmt.setMappingUint "tokenApprovalsSlot" (Expr.param "tokenId") (Expr.param "approved")
      , Stmt.stop ] := by
  exact ⟨[.requireClausesThenSetMappingUintParamsStop
    [] "tokenApprovalsSlot" "tokenId" "approved" 4
    erc721TokenApprovalsSlotFieldSlot (by decide)], rfl⟩

/-- ERC721.approve compilation correctness. -/
theorem erc721_approve_correctness (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment erc721Fields),
      supportedStmtFragmentsToStmts fragments =
        [ Stmt.setMappingUint "tokenApprovalsSlot" (Expr.param "tokenId") (Expr.param "approved")
        , Stmt.stop ] ∧
      execCompiledSupportedStmtFragments erc721Fields init fragments =
        execSourceSupportedStmtFragments erc721Fields init fragments :=
  compile_supported_stmt_list_semantics erc721Fields init _ erc721_approve_supported

-- ============================================================================
-- Constructor-level witness coverage (audit #1075)
-- ============================================================================

/-- Concrete witness for `requireClausesOnly` constructor. -/
theorem witness_requireClausesOnly_supported :
    SupportedStmtList simpleTokenFields [] := by
  exact ⟨[.requireClausesOnly []], rfl⟩

/-- Concrete witness for `requireClausesThenSetStorageLiteral` constructor. -/
theorem witness_requireClausesThenSetStorageLiteral_supported :
    SupportedStmtList simpleTokenFields
      [Stmt.setStorage "totalSupply" (Expr.literal 7)] := by
  exact ⟨[.requireClausesThenSetStorageLiteral
    [] "totalSupply" 2 7 simpleTokenTotalSupplyFieldResolution], rfl⟩

/-- Concrete witness for `requireClausesThenIteEqSetStorageLiterals` constructor. -/
theorem witness_requireClausesThenIteEqSetStorageLiterals_supported :
    SupportedStmtList simpleTokenFields
      [Stmt.ite (Expr.eq (Expr.literal 1) (Expr.literal 2))
        [Stmt.setStorage "totalSupply" (Expr.literal 3)]
        [Stmt.setStorage "totalSupply" (Expr.literal 4)]] := by
  exact ⟨[.requireClausesThenIteEqSetStorageLiterals
    [] "totalSupply" 2 1 2 3 4 simpleTokenTotalSupplyFieldResolution], rfl⟩

/-- Concrete witness for `requireClausesThenIteEqSetStorageThenReturnLiteral` constructor. -/
theorem witness_requireClausesThenIteEqSetStorageThenReturnLiteral_supported :
    SupportedStmtList simpleTokenFields
      [Stmt.ite (Expr.eq (Expr.literal 1) (Expr.literal 2))
        [Stmt.setStorage "totalSupply" (Expr.literal 3)]
        [Stmt.return (Expr.literal 4)]] := by
  exact ⟨[.requireClausesThenIteEqSetStorageThenReturnLiteral
    [] "totalSupply" 2 1 2 3 4 simpleTokenTotalSupplyFieldResolution], rfl⟩

/-- Concrete witness for `requireClausesThenIteEqReturnThenSetStorageLiteral` constructor. -/
theorem witness_requireClausesThenIteEqReturnThenSetStorageLiteral_supported :
    SupportedStmtList simpleTokenFields
      [Stmt.ite (Expr.eq (Expr.literal 1) (Expr.literal 2))
        [Stmt.return (Expr.literal 3)]
        [Stmt.setStorage "totalSupply" (Expr.literal 4)]] := by
  exact ⟨[.requireClausesThenIteEqReturnThenSetStorageLiteral
    [] "totalSupply" 2 1 2 3 4 simpleTokenTotalSupplyFieldResolution], rfl⟩

/-- Concrete witness for `requireClausesThenIteEqReturnLiterals` constructor. -/
theorem witness_requireClausesThenIteEqReturnLiterals_supported :
    SupportedStmtList simpleTokenFields
      [Stmt.ite (Expr.eq (Expr.literal 1) (Expr.literal 2))
        [Stmt.return (Expr.literal 3)]
        [Stmt.return (Expr.literal 4)]] := by
  exact ⟨[.requireClausesThenIteEqReturnLiterals [] 1 2 3 4], rfl⟩

/-- Concrete witness for `requireClausesThenIteEqThenIteEqReturnLiterals` constructor. -/
theorem witness_requireClausesThenIteEqThenIteEqReturnLiterals_supported :
    SupportedStmtList simpleTokenFields
      [Stmt.ite (Expr.eq (Expr.literal 1) (Expr.literal 2))
        [Stmt.ite (Expr.eq (Expr.literal 5) (Expr.literal 6))
          [Stmt.return (Expr.literal 3)]
          [Stmt.return (Expr.literal 4)]]
        [Stmt.return (Expr.literal 9)]] := by
  exact ⟨[.requireClausesThenIteEqThenIteEqReturnLiterals [] 1 2 5 6 3 4 9], rfl⟩

/-- Concrete witness for `requireClausesThenIteEqThenIteEqSetStorageLiteralsThenReturnLiteral` constructor. -/
theorem witness_requireClausesThenIteEqThenIteEqSetStorageLiteralsThenReturnLiteral_supported :
    SupportedStmtList simpleTokenFields
      [Stmt.ite (Expr.eq (Expr.literal 1) (Expr.literal 2))
        [Stmt.ite (Expr.eq (Expr.literal 5) (Expr.literal 6))
          [Stmt.setStorage "totalSupply" (Expr.literal 3)]
          [Stmt.setStorage "totalSupply" (Expr.literal 4)]]
        [Stmt.return (Expr.literal 9)]] := by
  exact ⟨[.requireClausesThenIteEqThenIteEqSetStorageLiteralsThenReturnLiteral
    [] "totalSupply" 2 1 2 5 6 3 4 9 simpleTokenTotalSupplyFieldResolution], rfl⟩

/-- Concrete witness for `requireClausesThenIteEqThenIteEqReturnLiteralsThenSetStorageLiteral` constructor. -/
theorem witness_requireClausesThenIteEqThenIteEqReturnLiteralsThenSetStorageLiteral_supported :
    SupportedStmtList simpleTokenFields
      [Stmt.ite (Expr.eq (Expr.literal 1) (Expr.literal 2))
        [Stmt.ite (Expr.eq (Expr.literal 5) (Expr.literal 6))
          [Stmt.return (Expr.literal 3)]
          [Stmt.return (Expr.literal 4)]]
        [Stmt.setStorage "totalSupply" (Expr.literal 9)]] := by
  exact ⟨[.requireClausesThenIteEqThenIteEqReturnLiteralsThenSetStorageLiteral
    [] "totalSupply" 2 1 2 5 6 3 4 9 simpleTokenTotalSupplyFieldResolution], rfl⟩

/-- Concrete witness for `requireClausesThenIteEqThenIteEqReturnLiteralsThenSetStorageLiteralThenReturnLiteral` constructor. -/
theorem witness_requireClausesThenIteEqThenIteEqReturnLiteralsThenSetStorageLiteralThenReturnLiteral_supported :
    SupportedStmtList simpleTokenFields
      [Stmt.ite (Expr.eq (Expr.literal 1) (Expr.literal 2))
        [Stmt.ite (Expr.eq (Expr.literal 5) (Expr.literal 6))
          [Stmt.return (Expr.literal 3)]
          [Stmt.return (Expr.literal 4)]]
        [Stmt.setStorage "totalSupply" (Expr.literal 8), Stmt.return (Expr.literal 9)]] := by
  exact ⟨[.requireClausesThenIteEqThenIteEqReturnLiteralsThenSetStorageLiteralThenReturnLiteral
    [] "totalSupply" 2 1 2 5 6 3 4 8 9 simpleTokenTotalSupplyFieldResolution], rfl⟩

/-- Concrete witness for `requireClausesThenIteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral` constructor. -/
theorem witness_requireClausesThenIteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral_supported :
    SupportedStmtList simpleTokenFields
      [Stmt.ite (Expr.eq (Expr.literal 1) (Expr.literal 2))
        [Stmt.ite (Expr.eq (Expr.literal 5) (Expr.literal 6))
          [Stmt.setStorage "totalSupply" (Expr.literal 3)]
          [Stmt.setStorage "totalSupply" (Expr.literal 4)]]
        [Stmt.setStorage "totalSupply" (Expr.literal 9)]] := by
  exact ⟨[.requireClausesThenIteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral
    [] "totalSupply" 2 1 2 5 6 3 4 9 simpleTokenTotalSupplyFieldResolution], rfl⟩

/-- Concrete witness for `requireClausesThenIteEqThenIteEqSetStorageThenReturnLiteralThenReturnLiteral` constructor. -/
theorem witness_requireClausesThenIteEqThenIteEqSetStorageThenReturnLiteralThenReturnLiteral_supported :
    SupportedStmtList simpleTokenFields
      [Stmt.ite (Expr.eq (Expr.literal 1) (Expr.literal 2))
        [Stmt.ite (Expr.eq (Expr.literal 5) (Expr.literal 6))
          [Stmt.setStorage "totalSupply" (Expr.literal 3)]
          [Stmt.return (Expr.literal 4)]]
        [Stmt.return (Expr.literal 9)]] := by
  exact ⟨[.requireClausesThenIteEqThenIteEqSetStorageThenReturnLiteralThenReturnLiteral
    [] "totalSupply" 2 1 2 5 6 3 4 9 simpleTokenTotalSupplyFieldResolution], rfl⟩

/-- Concrete witness for `requireClausesThenIteEqThenIteEqSetStorageThenReturnLiteralThenSetStorageLiteral` constructor. -/
theorem witness_requireClausesThenIteEqThenIteEqSetStorageThenReturnLiteralThenSetStorageLiteral_supported :
    SupportedStmtList simpleTokenFields
      [Stmt.ite (Expr.eq (Expr.literal 1) (Expr.literal 2))
        [Stmt.ite (Expr.eq (Expr.literal 5) (Expr.literal 6))
          [Stmt.setStorage "totalSupply" (Expr.literal 3)]
          [Stmt.return (Expr.literal 4)]]
        [Stmt.setStorage "totalSupply" (Expr.literal 9)]] := by
  exact ⟨[.requireClausesThenIteEqThenIteEqSetStorageThenReturnLiteralThenSetStorageLiteral
    [] "totalSupply" 2 1 2 5 6 3 4 9 simpleTokenTotalSupplyFieldResolution], rfl⟩

/-- Concrete witness for `requireClausesThenIteEqThenIteEqReturnThenSetStorageLiteralThenReturnLiteral` constructor. -/
theorem witness_requireClausesThenIteEqThenIteEqReturnThenSetStorageLiteralThenReturnLiteral_supported :
    SupportedStmtList simpleTokenFields
      [Stmt.ite (Expr.eq (Expr.literal 1) (Expr.literal 2))
        [Stmt.ite (Expr.eq (Expr.literal 5) (Expr.literal 6))
          [Stmt.return (Expr.literal 3)]
          [Stmt.setStorage "totalSupply" (Expr.literal 4)]]
        [Stmt.return (Expr.literal 9)]] := by
  exact ⟨[.requireClausesThenIteEqThenIteEqReturnThenSetStorageLiteralThenReturnLiteral
    [] "totalSupply" 2 1 2 5 6 3 4 9 simpleTokenTotalSupplyFieldResolution], rfl⟩

/-- Concrete witness for `requireClausesThenIteEqThenIteEqReturnThenSetStorageLiteralThenSetStorageLiteral` constructor. -/
theorem witness_requireClausesThenIteEqThenIteEqReturnThenSetStorageLiteralThenSetStorageLiteral_supported :
    SupportedStmtList simpleTokenFields
      [Stmt.ite (Expr.eq (Expr.literal 1) (Expr.literal 2))
        [Stmt.ite (Expr.eq (Expr.literal 5) (Expr.literal 6))
          [Stmt.return (Expr.literal 3)]
          [Stmt.setStorage "totalSupply" (Expr.literal 4)]]
        [Stmt.setStorage "totalSupply" (Expr.literal 9)]] := by
  exact ⟨[.requireClausesThenIteEqThenIteEqReturnThenSetStorageLiteralThenSetStorageLiteral
    [] "totalSupply" 2 1 2 5 6 3 4 9 simpleTokenTotalSupplyFieldResolution], rfl⟩

/-- Concrete witness for `requireClausesThenReturnLiteral` constructor. -/
theorem witness_requireClausesThenReturnLiteral_supported :
    SupportedStmtList simpleTokenFields [Stmt.return (Expr.literal 42)] := by
  exact ⟨[.requireClausesThenReturnLiteral [] 42], rfl⟩

/-- Concrete witness for `requireClausesThenLetReturnLocalLiteral` constructor. -/
theorem witness_requireClausesThenLetReturnLocalLiteral_supported :
    SupportedStmtList simpleTokenFields
      [Stmt.letVar "tmp" (Expr.literal 42), Stmt.return (Expr.localVar "tmp")] := by
  exact ⟨[.requireClausesThenLetReturnLocalLiteral [] "tmp" 42], rfl⟩

/-- Concrete witness for `requireClausesThenLetSetStorageLocalLiteral` constructor. -/
theorem witness_requireClausesThenLetSetStorageLocalLiteral_supported :
    SupportedStmtList simpleTokenFields
      [Stmt.letVar "tmp" (Expr.literal 1), Stmt.setStorage "totalSupply" (Expr.localVar "tmp")] := by
  exact ⟨[.requireClausesThenLetSetStorageLocalLiteral
    [] "totalSupply" "tmp" 2 1 simpleTokenTotalSupplyFieldResolution], rfl⟩

/-- Concrete witness for `requireClausesThenLetAssignSetStorageLocalLiteral` constructor. -/
theorem witness_requireClausesThenLetAssignSetStorageLocalLiteral_supported :
    SupportedStmtList simpleTokenFields
      [ Stmt.letVar "tmp" (Expr.literal 1)
      , Stmt.assignVar "tmp" (Expr.literal 2)
      , Stmt.setStorage "totalSupply" (Expr.localVar "tmp")
      ] := by
  exact ⟨[.requireClausesThenLetAssignSetStorageLocalLiteral
    [] "totalSupply" "tmp" 2 1 2 simpleTokenTotalSupplyFieldResolution], rfl⟩

/-- Concrete witness for `requireClausesThenLetAssignAddSetStorageLocalLiteral` constructor. -/
theorem witness_requireClausesThenLetAssignAddSetStorageLocalLiteral_supported :
    SupportedStmtList simpleTokenFields
      [ Stmt.letVar "tmp" (Expr.literal 1)
      , Stmt.assignVar "tmp" (Expr.add (Expr.localVar "tmp") (Expr.literal 2))
      , Stmt.setStorage "totalSupply" (Expr.localVar "tmp")
      ] := by
  exact ⟨[.requireClausesThenLetAssignAddSetStorageLocalLiteral
    [] "totalSupply" "tmp" 2 1 2 simpleTokenTotalSupplyFieldResolution], rfl⟩

/-- Concrete witness for `requireClausesThenLetAssignSubSetStorageLocalLiteral` constructor. -/
theorem witness_requireClausesThenLetAssignSubSetStorageLocalLiteral_supported :
    SupportedStmtList simpleTokenFields
      [ Stmt.letVar "tmp" (Expr.literal 1)
      , Stmt.assignVar "tmp" (Expr.sub (Expr.localVar "tmp") (Expr.literal 2))
      , Stmt.setStorage "totalSupply" (Expr.localVar "tmp")
      ] := by
  exact ⟨[.requireClausesThenLetAssignSubSetStorageLocalLiteral
    [] "totalSupply" "tmp" 2 1 2 simpleTokenTotalSupplyFieldResolution], rfl⟩

/-- Concrete witness for `requireClausesThenLetAssignMulSetStorageLocalLiteral` constructor. -/
theorem witness_requireClausesThenLetAssignMulSetStorageLocalLiteral_supported :
    SupportedStmtList simpleTokenFields
      [ Stmt.letVar "tmp" (Expr.literal 1)
      , Stmt.assignVar "tmp" (Expr.mul (Expr.localVar "tmp") (Expr.literal 2))
      , Stmt.setStorage "totalSupply" (Expr.localVar "tmp")
      ] := by
  exact ⟨[.requireClausesThenLetAssignMulSetStorageLocalLiteral
    [] "totalSupply" "tmp" 2 1 2 simpleTokenTotalSupplyFieldResolution], rfl⟩

/-- Concrete witness for `requireClausesThenReturnMappingCaller` constructor. -/
theorem witness_requireClausesThenReturnMappingCaller_supported :
    SupportedStmtList simpleTokenFields
      [Stmt.return (Expr.mapping "balances" Expr.caller)] := by
  exact ⟨[.requireClausesThenReturnMappingCaller
    [] "balances" 1 simpleTokenBalancesFieldSlot], rfl⟩

end Verity.Core.Free
