import Verity.Core.Free.TypedIR
import Verity.Core.Free.ContractStep
import Verity.Core.Free.TypedIRCompiler
import Verity.Core.Free.TypedIRCompilerCorrectness
import Verity.Core.Free.TypedIRLowering
import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Specs

namespace Verity.Core.Free

def x : TVar := { id := 0, ty := .uint256 }
def y : TVar := { id := 1, ty := .uint256 }
def flag : TVar := { id := 2, ty := .bool }
def owner : TVar := { id := 3, ty := .address }

/-- Expression typing sanity check: uint arithmetic stays in `Ty.uint256`. -/
example : TExpr .uint256 := TExpr.add (TExpr.var x) (TExpr.var y)

/-- Statement typing sanity check: destination and rhs types must match. -/
example : TStmt := TStmt.assign x (TExpr.add (TExpr.var x) (TExpr.uintLit 1))

/-- Branching sanity check: condition must be statically boolean. -/
example : TStmt := TStmt.if_
  (TExpr.var flag)
  [TStmt.setStorage 0 (TExpr.var x)]
  [TStmt.revert "bad condition"]

/-- Block construction sanity check with typed declarations and statements. -/
example : TBlock where
  params := [x]
  locals := [y, flag]
  body :=
    [ TStmt.let_ y (TExpr.add (TExpr.var x) (TExpr.uintLit 1))
    , TStmt.assign x (TExpr.var y)
    , TStmt.if_ (TExpr.var flag)
        [TStmt.setStorage 0 (TExpr.var x)]
        [TStmt.revert "flag=false"]
    ]

def baseWorld : Verity.ContractState :=
  { Verity.defaultState with
    sender := 7
    thisAddress := 9
    msgValue := 11
    blockTimestamp := 13
  }

def baseState : TExecState :=
  { world := baseWorld
    vars :=
      { uint256 := fun
          | 0 => 5
          | 1 => 8
          | _ => 0
        bool := fun
          | 2 => true
          | _ => false
        address := fun
          | 3 => 42
          | _ => 0
      } }

/-- `evalTExpr` reads variables and preserves typed arithmetic. -/
example :
    evalTExpr baseState (TExpr.add (TExpr.var x) (TExpr.var y)) =
      Verity.Core.Uint256.add 5 8 := by
  simp [baseState, x, y, evalTExpr, TVars.get]

/-- `evalTExpr` division matches Uint256 semantics (divide by zero returns zero). -/
example :
    evalTExpr baseState (TExpr.div (TExpr.uintLit 42) (TExpr.uintLit 0)) =
      (0 : Verity.Core.Uint256) := by
  simp [evalTExpr, Verity.Core.Uint256.div]

/-- `evalTExpr` modulo matches Uint256 semantics (mod by zero returns zero). -/
example :
    evalTExpr baseState (TExpr.mod (TExpr.uintLit 10) (TExpr.uintLit 0)) =
      (0 : Verity.Core.Uint256) := by
  simp [evalTExpr, Verity.Core.Uint256.mod]

/-- One-step evaluator reductions are available through the dedicated `ir_step` simp set. -/
example :
    evalTBlock baseState { params := [], locals := [], body := [] } = .ok baseState := by
  contract_step

/-- `contract_step` also simplifies single-step expression reductions. -/
example :
    evalTExpr baseState (TExpr.var x) = (5 : Verity.Core.Uint256) := by
  contract_step
  simp [baseState, x, TVars.get]

def compileDivExprSucceeds : Bool :=
  match (compileStmts []
      [Compiler.CompilationModel.Stmt.return
        (Compiler.CompilationModel.Expr.div
          (Compiler.CompilationModel.Expr.literal 10)
          (Compiler.CompilationModel.Expr.literal 3))]).run {} with
  | .ok _ => true
  | .error _ => false

def compileModExprSucceeds : Bool :=
  match (compileStmts []
      [Compiler.CompilationModel.Stmt.return
        (Compiler.CompilationModel.Expr.mod
          (Compiler.CompilationModel.Expr.literal 10)
          (Compiler.CompilationModel.Expr.literal 3))]).run {} with
  | .ok _ => true
  | .error _ => false

def compileRawLogSucceeds : Bool :=
  match (compileStmts []
      [Compiler.CompilationModel.Stmt.rawLog
        [Compiler.CompilationModel.Expr.literal 1, Compiler.CompilationModel.Expr.literal 2]
        (Compiler.CompilationModel.Expr.literal 0)
        (Compiler.CompilationModel.Expr.literal 64)]).run {} with
  | .ok _ => true
  | .error _ => false

def compileRawLogLoweringShapeOk : Bool :=
  match (compileStmts []
      [Compiler.CompilationModel.Stmt.rawLog
        [Compiler.CompilationModel.Expr.literal 1, Compiler.CompilationModel.Expr.literal 2]
        (Compiler.CompilationModel.Expr.literal 0)
        (Compiler.CompilationModel.Expr.literal 64)]).run {} with
  | .ok st =>
      match lowerTStmts st.2.body.toList with
      | [.expr (.call "log2" [.lit 0, .lit 64, .lit 1, .lit 2])] => true
      | _ => false
  | .error _ => false

def compileRawLogTooManyTopicsFails : Bool :=
  match (compileStmts []
      [Compiler.CompilationModel.Stmt.rawLog
        [ Compiler.CompilationModel.Expr.literal 1
        , Compiler.CompilationModel.Expr.literal 2
        , Compiler.CompilationModel.Expr.literal 3
        , Compiler.CompilationModel.Expr.literal 4
        , Compiler.CompilationModel.Expr.literal 5
        ]
        (Compiler.CompilationModel.Expr.literal 0)
        (Compiler.CompilationModel.Expr.literal 64)]).run {} with
  | .ok _ => false
  | .error msg => msg = "Typed IR compile error: rawLog supports at most 4 topics, got 5"

/-- Typed-IR compiler accepts source-level `Expr.div`. -/
example : compileDivExprSucceeds = true := by native_decide

/-- Typed-IR compiler accepts source-level `Expr.mod`. -/
example : compileModExprSucceeds = true := by native_decide

/-- Typed-IR compiler accepts source-level `Stmt.rawLog`. -/
example : compileRawLogSucceeds = true := by native_decide

/-- Typed-IR compiler emits the expected typed `rawLog` statement shape. -/
example : compileRawLogLoweringShapeOk = true := by native_decide

/-- Typed-IR compiler rejects `rawLog` with more than 4 topics. -/
example : compileRawLogTooManyTopicsFails = true := by native_decide

/-- Context expressions read from world/environment. -/
example :
    evalTExpr baseState TExpr.sender = (7 : Verity.Core.Address) := by
  simp [baseState, evalTExpr, baseWorld, Verity.Env.ofWorld]

def envOverrideState : TExecState :=
  { world := baseWorld
    env := { sender := 99, thisAddress := 100, msgValue := 101, blockTimestamp := 102 }
    vars := baseState.vars }

/-- Context expressions read from explicit `TExecState.env`, not from world fields. -/
example :
    evalTExpr envOverrideState TExpr.sender = (99 : Verity.Core.Address) := by
  simp [envOverrideState, evalTExpr]

/-- Storage updates do not mutate explicit execution environment fields. -/
example :
    match evalTStmt envOverrideState (TStmt.setStorage 8 (TExpr.uintLit 55)) with
    | .ok s' => s'.env.sender = (99 : Verity.Core.Address)
    | .revert _ => False := by
  simp [envOverrideState, evalTStmt, evalTStmtFuel, defaultEvalFuel]

/-- Assignment updates the typed variable environment. -/
example :
    match evalTStmt baseState (TStmt.assign x (TExpr.uintLit 99)) with
    | .ok s' => s'.vars.get x = (99 : Verity.Core.Uint256)
    | .revert _ => True := by
  simp [evalTStmt, evalTStmtFuel, defaultEvalFuel]

/-- Storage updates are reflected in the output execution world. -/
example :
    match evalTStmt baseState (TStmt.setStorage 4 (TExpr.uintLit 123)) with
    | .ok s' => s'.world.storage 4 = (123 : Verity.Core.Uint256)
    | .revert _ => True := by
  simp [evalTStmt, evalTStmtFuel, defaultEvalFuel]

/-- Raw logs are recorded as append-only event entries. -/
example :
    match evalTStmt baseState (TStmt.rawLog [TExpr.uintLit 1, TExpr.uintLit 2] (TExpr.uintLit 0) (TExpr.uintLit 64)) with
    | .ok s' => s'.world.events.length = baseState.world.events.length + 1
    | .revert _ => False := by
  simp [evalTStmt, evalTStmtFuel, defaultEvalFuel]
  rfl

/-- Branching and block execution compose through `evalTBlock`. -/
example :
    match evalTStmt baseState
      (TStmt.if_ (TExpr.boolLit true)
        []
        [TStmt.revert "no"]) with
    | .ok _ => True
    | .revert _ => False := by
  simp [evalTStmt, evalTStmtFuel, evalTStmtsFuel, defaultEvalFuel]

/-- Explicit revert in the block propagates as `Except.error`. -/
example :
    evalTBlock baseState
      { params := []
        locals := []
        body := [TStmt.revert "halt"] } = .revert "halt" := by
  simp [evalTBlock, evalTStmts, evalTStmtsFuel, evalTStmtFuel, defaultEvalFuel]

open Compiler.Yul
open Compiler.Proofs.IRGeneration

/-- Lowering emits a Yul `div` call for typed division. -/
example :
    lowerTExpr (TExpr.div (TExpr.uintLit 10) (TExpr.uintLit 3)) =
      .call "div" [.lit 10, .lit 3] := by
  rfl

/-- Lowering emits a Yul `mod` call for typed modulo. -/
example :
    lowerTExpr (TExpr.mod (TExpr.uintLit 10) (TExpr.uintLit 3)) =
      .call "mod" [.lit 10, .lit 3] := by
  rfl

/-- Lowering emits `log2` for typed raw logs with two topics. -/
example :
    lowerTStmts [TStmt.rawLog [TExpr.uintLit 1, TExpr.uintLit 2] (TExpr.uintLit 0) (TExpr.uintLit 64)] =
      [.expr (.call "log2" [.lit 0, .lit 64, .lit 1, .lit 2])] := by
  rfl

/-- Lowering emits `log0` when the topic list is empty. -/
example :
    lowerTStmts [TStmt.rawLog [] (TExpr.uintLit 0) (TExpr.uintLit 32)] =
      [.expr (.call "log0" [.lit 0, .lit 32])] := by
  rfl

def counterTmp : TVar := { id := 10, ty := .uint256 }

/-- Typed IR block equivalent to Counter.increment (`count := count + 1`). -/
def counterIncrementTBlock : TBlock where
  params := []
  locals := [counterTmp]
  body :=
    [ TStmt.let_ counterTmp (TExpr.getStorage 0)
    , TStmt.assign counterTmp (TExpr.add (TExpr.var counterTmp) (TExpr.uintLit 1))
    , TStmt.setStorage 0 (TExpr.var counterTmp)
    ]

/-- Existing untyped IR program equivalent to `counterIncrementTBlock`. -/
def counterIncrementIR : List YulStmt :=
  [ .let_ "tmp" (.call "sload" [.lit 0])
  , .assign "tmp" (.call "add" [.ident "tmp", .lit 1])
  , .expr (.call "sstore" [.lit 0, .ident "tmp"])
  ]

def counterTypedInitWorld : Verity.ContractState :=
  { «storage» := fun i => if i = 0 then 41 else 0
    storageAddr := fun _ => 0
    storageMap := fun _ _ => 0
    storageMapUint := fun _ _ => 0
    storageMap2 := fun _ _ _ => 0
    sender := 0
    thisAddress := 0
    msgValue := 0
    blockTimestamp := 0
    knownAddresses := fun _ => Verity.Core.FiniteAddressSet.empty
    events := [] }

def counterTypedInit : TExecState :=
  { world := counterTypedInitWorld }

def counterIRInit : IRState :=
  { vars := []
    «storage» := fun i => if i = 0 then 41 else 0
    memory := fun _ => 0
    calldata := []
    returnValue := none
    sender := 0
    selector := 0 }

def counterTypedFinalSlot : Option Nat :=
  match evalTBlock counterTypedInit counterIncrementTBlock with
  | .ok s => some ((s.world.storage 0 : Verity.Core.Uint256) : Nat)
  | .revert _ => none

def counterIRFinalSlot : Option Nat :=
  match execIRStmts 32 counterIRInit counterIncrementIR with
  | .continue s => some (s.storage 0)
  | _ => none

/-- Golden test: typed Counter increment matches existing IR evaluation. -/
example : counterTypedFinalSlot = counterIRFinalSlot := by
  native_decide

def simpleStorageValue : TVar := { id := 20, ty := .uint256 }

/-- Typed IR block equivalent to SimpleStorage.store(v). -/
def simpleStorageStoreTBlock : TBlock where
  params := [simpleStorageValue]
  locals := []
  body := [TStmt.setStorage 0 (TExpr.var simpleStorageValue)]

/-- Existing untyped IR program equivalent to `simpleStorageStoreTBlock`. -/
def simpleStorageStoreIR : List YulStmt :=
  [ .expr (.call "sstore" [.lit 0, .ident "value"]) ]

def simpleStorageTypedInitWorld : Verity.ContractState :=
  { «storage» := fun i => if i = 0 then 5 else 0
    storageAddr := fun _ => 0
    storageMap := fun _ _ => 0
    storageMapUint := fun _ _ => 0
    storageMap2 := fun _ _ _ => 0
    sender := 0
    thisAddress := 0
    msgValue := 0
    blockTimestamp := 0
    knownAddresses := fun _ => Verity.Core.FiniteAddressSet.empty
    events := [] }

def simpleStorageTypedInit : TExecState :=
  { world := simpleStorageTypedInitWorld
    vars := { uint256 := fun
      | 20 => 77
      | _ => 0 } }

def simpleStorageIRInit : IRState :=
  (IRState.initial 0).setVar "value" 77

def simpleStorageIRInitWithStorage : IRState :=
  { vars := simpleStorageIRInit.vars
    «storage» := fun i => if i = 0 then 5 else 0
    memory := simpleStorageIRInit.memory
    calldata := simpleStorageIRInit.calldata
    returnValue := simpleStorageIRInit.returnValue
    sender := simpleStorageIRInit.sender
    selector := simpleStorageIRInit.selector }

def simpleStorageTypedFinalSlot : Option Nat :=
  match evalTBlock simpleStorageTypedInit simpleStorageStoreTBlock with
  | .ok s => some ((s.world.storage 0 : Verity.Core.Uint256) : Nat)
  | .revert _ => none

def simpleStorageIRFinalSlot : Option Nat :=
  match execIRStmts 16 simpleStorageIRInitWithStorage simpleStorageStoreIR with
  | .continue s => some (s.storage 0)
  | _ => none

/-- Golden test: typed SimpleStorage store matches existing IR evaluation. -/
example : simpleStorageTypedFinalSlot = simpleStorageIRFinalSlot := by
  native_decide

private def tVarValueNat (state : Verity.Core.Free.TExecState.{0}) (v : TVar) : Nat :=
  match v with
  | ⟨id, .uint256⟩ => state.vars.uint256 id
  | ⟨id, .address⟩ => state.vars.address id
  | ⟨id, .bool⟩ => if state.vars.bool id then 1 else 0
  | ⟨_, .unit⟩ => 0

private def mkIRStateFromTyped (state : Verity.Core.Free.TExecState.{0}) (block : TBlock) : IRState :=
  let initVars : List (String × Nat) :=
    (block.params ++ block.locals).map (fun v => (tVarName v, tVarValueNat state v))
  -- Merge typed storage fields into flat EVM storage.  In the EVM there is a
  -- single `sload`/`sstore` namespace; the typed IR model splits it into
  -- `storage` (uint256) and `storageAddr` (address) for type safety.  Each
  -- slot is used by at most one field type, so we overlay the non-default value.
  let flatStorage : Nat → Nat := fun i =>
    let u : Nat := state.world.storage i
    let a : Nat := state.world.storageAddr i
    if a != 0 then a else u
  IRState.mk
    initVars
    flatStorage
    (fun _ => 0)
    []
    none
    state.env.sender
    0
    []

private def execLoweredSlot0 (fuel : Nat) (state : IRState) (block : TBlock) : Option Nat :=
  match execIRStmts fuel state (lowerTBlock block) with
  | .continue s => some (s.storage 0)
  | .stop s => some (s.storage 0)
  | .return _ s => some (s.storage 0)
  | .revert _ => none

private def execLoweredReturn (fuel : Nat) (state : IRState) (block : TBlock) : Option Nat :=
  match execIRStmts fuel state (lowerTBlock block) with
  | .return ret _ => some ret
  | _ => none

private def execLoweredState (fuel : Nat) (state : IRState) (block : TBlock) : Option IRState :=
  match execIRStmts fuel state (lowerTBlock block) with
  | .continue s => some s
  | .stop s => some s
  | .return _ s => some s
  | .revert _ => none

/-- Golden test: lowering typed Counter block to Yul preserves storage-slot result. -/
example :
    execLoweredSlot0 64 (mkIRStateFromTyped counterTypedInit counterIncrementTBlock) counterIncrementTBlock =
      counterTypedFinalSlot := by
  native_decide

/-- Golden test: lowering typed SimpleStorage block to Yul preserves storage-slot result. -/
example :
    execLoweredSlot0 64 (mkIRStateFromTyped simpleStorageTypedInit simpleStorageStoreTBlock) simpleStorageStoreTBlock =
      simpleStorageTypedFinalSlot := by
  native_decide

def compiledCounterIncrementFinalSlot : Option Nat :=
  match compileFunctionNamed Compiler.Specs.counterSpec "increment" with
  | .error _ => none
  | .ok block =>
      match evalTBlock counterTypedInit block with
      | .ok s => some ((s.world.storage 0 : Verity.Core.Uint256) : Nat)
      | .revert _ => none

/-- Golden test: CompilationModel->typed-IR compiler preserves Counter.increment storage effect. -/
example : compiledCounterIncrementFinalSlot = counterIRFinalSlot := by
  native_decide

def compiledSimpleStorageStoreFinalSlot : Option Nat :=
  match compileFunctionNamed Compiler.Specs.simpleStorageSpec "store" with
  | .error _ => none
  | .ok block =>
      match block.params with
      | [] => none
      | valueParam :: _ =>
          let init : TExecState :=
            { world := simpleStorageTypedInitWorld
              vars := { uint256 := fun
                | i => if i = valueParam.id then 77 else 0 } }
          match evalTBlock init block with
          | .ok s => some ((s.world.storage 0 : Verity.Core.Uint256) : Nat)
          | .revert _ => none

/-- Golden test: CompilationModel->typed-IR compiler preserves SimpleStorage.store storage effect. -/
example : compiledSimpleStorageStoreFinalSlot = simpleStorageIRFinalSlot := by
  native_decide

def compiledCounterLoweredFinalSlot : Option Nat :=
  match compileFunctionNamed Compiler.Specs.counterSpec "increment" with
  | .error _ => none
  | .ok block =>
      execLoweredSlot0 256 (mkIRStateFromTyped counterTypedInit block) block

/-- Golden test: compiled typed Counter block lowers to Yul with matching final storage. -/
example : compiledCounterLoweredFinalSlot = compiledCounterIncrementFinalSlot := by
  native_decide

def compiledCounterDecrementFinalSlot : Option Nat :=
  let initWorld : Verity.ContractState :=
    { counterTypedInitWorld with «storage» := fun i => if i = 0 then 41 else 0 }
  let initTyped : TExecState := { world := initWorld }
  match compileFunctionNamed Compiler.Specs.counterSpec "decrement" with
  | .error _ => none
  | .ok block =>
      match evalTBlock initTyped block with
      | .ok s => some ((s.world.storage 0 : Verity.Core.Uint256) : Nat)
      | .revert _ => none

def compiledCounterDecrementLoweredFinalSlot : Option Nat :=
  let initWorld : Verity.ContractState :=
    { counterTypedInitWorld with «storage» := fun i => if i = 0 then 41 else 0 }
  let initTyped : TExecState := { world := initWorld }
  match compileFunctionNamed Compiler.Specs.counterSpec "decrement" with
  | .error _ => none
  | .ok block =>
      execLoweredSlot0 256 (mkIRStateFromTyped initTyped block) block

/-- End-to-end Counter decrement: typed IR lowering preserves storage effect. -/
example : compiledCounterDecrementLoweredFinalSlot = compiledCounterDecrementFinalSlot := by
  native_decide

def compiledCounterGetCountReturn : Option Nat :=
  let initWorld : Verity.ContractState :=
    { counterTypedInitWorld with «storage» := fun i => if i = 0 then 41 else 0 }
  let initTyped : TExecState := { world := initWorld }
  match compileFunctionNamed Compiler.Specs.counterSpec "getCount" with
  | .error _ => none
  | .ok block =>
      execLoweredReturn 256 (mkIRStateFromTyped initTyped block) block

/-- End-to-end Counter getCount: typed IR pipeline returns slot-0 value. -/
example : compiledCounterGetCountReturn = some 41 := by
  native_decide

def compiledSimpleStorageLoweredFinalSlot : Option Nat :=
  match compileFunctionNamed Compiler.Specs.simpleStorageSpec "store" with
  | .error _ => none
  | .ok block =>
      match block.params with
      | [] => none
      | valueParam :: _ =>
          let init : Verity.Core.Free.TExecState.{0} :=
            { world := simpleStorageTypedInitWorld
              vars := { uint256 := fun
                | i => if i = valueParam.id then 77 else 0 } }
          execLoweredSlot0 256 (mkIRStateFromTyped init block) block

/-- Golden test: compiled typed SimpleStorage block lowers to Yul with matching final storage. -/
example : compiledSimpleStorageLoweredFinalSlot = compiledSimpleStorageStoreFinalSlot := by
  native_decide

def compiledSimpleStorageRetrieveReturn : Option Nat :=
  let initWorld : Verity.ContractState :=
    { simpleStorageTypedInitWorld with «storage» := fun i => if i = 0 then 77 else 0 }
  let initTyped : TExecState := { world := initWorld }
  match compileFunctionNamed Compiler.Specs.simpleStorageSpec "retrieve" with
  | .error _ => none
  | .ok block =>
      execLoweredReturn 256 (mkIRStateFromTyped initTyped block) block

/-- End-to-end SimpleStorage retrieve: typed IR pipeline returns slot-0 value. -/
example : compiledSimpleStorageRetrieveReturn = some 77 := by
  native_decide

def compiledSimpleStorageStoreRetrieveRoundtrip : Option Nat :=
  match compileFunctionNamed Compiler.Specs.simpleStorageSpec "store",
        compileFunctionNamed Compiler.Specs.simpleStorageSpec "retrieve" with
  | .ok storeBlock, .ok retrieveBlock =>
      match storeBlock.params with
      | [] => none
      | valueParam :: _ =>
          let init : Verity.Core.Free.TExecState.{0} :=
            { world := simpleStorageTypedInitWorld
              vars := { uint256 := fun
                | i => if i = valueParam.id then 99 else 0 } }
          match execLoweredState 256 (mkIRStateFromTyped init storeBlock) storeBlock with
          | none => none
          | some postStore =>
              execLoweredReturn 256 postStore retrieveBlock
  | _, _ => none

/-- End-to-end SimpleStorage store→retrieve roundtrip through typed IR pipeline. -/
example : compiledSimpleStorageStoreRetrieveRoundtrip = some 99 := by
  native_decide

/-- Smoke test: Ledger.transfer compiles successfully (exercises bool→uint256 coercion). -/
def compiledLedgerTransferBlock : Option TBlock :=
  match compileFunctionNamed Compiler.Specs.ledgerSpec "transfer" with
  | .ok block => some block
  | .error _ => none

example : compiledLedgerTransferBlock.isSome = true := by
  native_decide

/-- End-to-end Ledger.transfer: non-self transfer updates both balances correctly. -/
def compiledLedgerTransferResult : Option (Nat × Nat) :=
  match compileFunctionNamed Compiler.Specs.ledgerSpec "transfer" with
  | .error _ => none
  | .ok block =>
      match block.params with
      | [toParam, amountParam] =>
          let initWorld : Verity.ContractState :=
            { Verity.defaultState with
              -- sender (address 1) has balance 100 in mapping slot 0
              storageMap := fun i addr =>
                if i == 0 && addr == 1 then 100
                else if i == 0 && addr == 2 then 50
                else 0
              sender := 1 }
          let init : TExecState :=
            { world := initWorld
              vars := { address := fun i =>
                          if i = toParam.id then 2 else 0
                        uint256 := fun i =>
                          if i = amountParam.id then 30 else 0 } }
          match evalTBlock init block with
          | .ok s => some (s.world.storageMap 0 1, s.world.storageMap 0 2)
          | .revert _ => none
      | _ => none

/-- Ledger.transfer(to=2, amount=30): sender balance 100→70, recipient balance 50→80. -/
example : compiledLedgerTransferResult = some (70, 80) := by
  native_decide

/-- Smoke test: Owned.getOwner compiles successfully (exercises returnAddr path). -/
def compiledOwnedGetOwnerBlock : Option TBlock :=
  match compileFunctionNamed Compiler.Specs.ownedSpec "getOwner" with
  | .ok block => some block
  | .error _ => none

example : compiledOwnedGetOwnerBlock.isSome = true := by
  native_decide

/-- End-to-end Owned.getOwner: returns the stored owner address via typed IR lowering. -/
def compiledOwnedGetOwnerReturn : Option Nat :=
  match compileFunctionNamed Compiler.Specs.ownedSpec "getOwner" with
  | .error _ => none
  | .ok block =>
      let initWorld : Verity.ContractState :=
        { Verity.defaultState with storageAddr := fun i => if i = 0 then 42 else 0 }
      let init : TExecState := { world := initWorld }
      execLoweredReturn 256 (mkIRStateFromTyped init block) block

/-- Owned.getOwner returns stored owner address (42) through the full pipeline. -/
example : compiledOwnedGetOwnerReturn = some 42 := by
  native_decide

/-- Smoke test: Owned.transferOwnership compiles successfully (exercises requireOwner + setStorageAddr). -/
def compiledOwnedTransferOwnershipBlock : Option TBlock :=
  match compileFunctionNamed Compiler.Specs.ownedSpec "transferOwnership" with
  | .ok block => some block
  | .error _ => none

example : compiledOwnedTransferOwnershipBlock.isSome = true := by
  native_decide

/-- End-to-end Owned.transferOwnership (happy path): owner transfers ownership. -/
def compiledOwnedTransferOwnershipSuccess : Option Nat :=
  match compileFunctionNamed Compiler.Specs.ownedSpec "transferOwnership" with
  | .error _ => none
  | .ok block =>
      match block.params with
      | [newOwnerParam] =>
          let initWorld : Verity.ContractState :=
            { Verity.defaultState with
              storageAddr := fun i => if i = 0 then 42 else 0
              sender := 42 }
          let init : TExecState :=
            { world := initWorld
              vars := { address := fun i =>
                          if i = newOwnerParam.id then 99 else 0 } }
          match evalTBlock init block with
          | .ok s => some (s.world.storageAddr 0 : Nat)
          | .revert _ => none
      | _ => none

/-- Owned.transferOwnership(newOwner=99) by owner (42): owner slot becomes 99. -/
example : compiledOwnedTransferOwnershipSuccess = some 99 := by native_decide

/-- End-to-end Owned.transferOwnership (revert path): non-owner is rejected. -/
def compiledOwnedTransferOwnershipReverts : Bool :=
  match compileFunctionNamed Compiler.Specs.ownedSpec "transferOwnership" with
  | .error _ => false
  | .ok block =>
      match block.params with
      | [newOwnerParam] =>
          let initWorld : Verity.ContractState :=
            { Verity.defaultState with
              storageAddr := fun i => if i = 0 then 42 else 0
              sender := 99 }
          let init : TExecState :=
            { world := initWorld
              vars := { address := fun i =>
                          if i = newOwnerParam.id then 99 else 0 } }
          match evalTBlock init block with
          | .ok _ => false
          | .revert _ => true
      | _ => false

/-- Owned.transferOwnership by non-owner (99): reverts with "Not owner". -/
example : compiledOwnedTransferOwnershipReverts = true := by native_decide

/-- Helper: check that compilation succeeds. -/
private def compilesOk (spec : Compiler.CompilationModel.CompilationModel) (fn : String) : Bool :=
  match compileFunctionNamed spec fn with
  | .ok _ => true
  | .error _ => false

/-- Smoke test: all Ledger spec functions compile to typed IR. -/
example : compilesOk Compiler.Specs.ledgerSpec "deposit" = true := by native_decide
example : compilesOk Compiler.Specs.ledgerSpec "withdraw" = true := by native_decide
example : compilesOk Compiler.Specs.ledgerSpec "getBalance" = true := by native_decide

/-- End-to-end Ledger.deposit: increases sender balance via mapping write. -/
def compiledLedgerDepositResult : Option Nat :=
  match compileFunctionNamed Compiler.Specs.ledgerSpec "deposit" with
  | .error _ => none
  | .ok block =>
      match block.params with
      | [amountParam] =>
          let initWorld : Verity.ContractState :=
            { Verity.defaultState with
              storageMap := fun i addr =>
                if i == 0 && addr == 1 then 100 else 0
              sender := 1 }
          let init : TExecState :=
            { world := initWorld
              vars := { uint256 := fun i =>
                          if i = amountParam.id then 50 else 0 } }
          match evalTBlock init block with
          | .ok s => some (s.world.storageMap 0 1)
          | .revert _ => none
      | _ => none

/-- Ledger.deposit(amount=50): sender balance 100→150. -/
example : compiledLedgerDepositResult = some 150 := by native_decide

/-- End-to-end Ledger.withdraw (happy path): sufficient balance succeeds. -/
def compiledLedgerWithdrawSuccess : Option Nat :=
  match compileFunctionNamed Compiler.Specs.ledgerSpec "withdraw" with
  | .error _ => none
  | .ok block =>
      match block.params with
      | [amountParam] =>
          let initWorld : Verity.ContractState :=
            { Verity.defaultState with
              storageMap := fun i addr =>
                if i == 0 && addr == 1 then 100 else 0
              sender := 1 }
          let init : TExecState :=
            { world := initWorld
              vars := { uint256 := fun i =>
                          if i = amountParam.id then 30 else 0 } }
          match evalTBlock init block with
          | .ok s => some (s.world.storageMap 0 1)
          | .revert _ => none
      | _ => none

/-- Ledger.withdraw(amount=30): sender balance 100→70 (require passes). -/
example : compiledLedgerWithdrawSuccess = some 70 := by native_decide

/-- End-to-end Ledger.withdraw (revert path): insufficient balance reverts. -/
def compiledLedgerWithdrawReverts : Bool :=
  match compileFunctionNamed Compiler.Specs.ledgerSpec "withdraw" with
  | .error _ => false
  | .ok block =>
      match block.params with
      | [amountParam] =>
          let initWorld : Verity.ContractState :=
            { Verity.defaultState with
              storageMap := fun i addr =>
                if i == 0 && addr == 1 then 10 else 0
              sender := 1 }
          let init : TExecState :=
            { world := initWorld
              vars := { uint256 := fun i =>
                          if i = amountParam.id then 50 else 0 } }
          match evalTBlock init block with
          | .ok _ => false
          | .revert _ => true
      | _ => false

/-- Ledger.withdraw(amount=50) with balance=10: reverts with "Insufficient balance". -/
example : compiledLedgerWithdrawReverts = true := by native_decide

/-- End-to-end OwnedCounter.increment (happy path): owner can increment. -/
def compiledOwnedCounterIncrementSuccess : Option Nat :=
  match compileFunctionNamed Compiler.Specs.ownedCounterSpec "increment" with
  | .error _ => none
  | .ok block =>
      let initWorld : Verity.ContractState :=
        { Verity.defaultState with
          storageAddr := fun i => if i = 0 then 42 else 0
          «storage» := fun i => if i = 1 then 10 else 0
          sender := 42 }
      let init : TExecState := { world := initWorld }
      match evalTBlock init block with
      | .ok s => some (s.world.storage 1)
      | .revert _ => none

/-- OwnedCounter.increment by owner (42): count 10→11. -/
example : compiledOwnedCounterIncrementSuccess = some 11 := by native_decide

/-- End-to-end OwnedCounter.increment (revert path): non-owner is rejected. -/
def compiledOwnedCounterIncrementReverts : Bool :=
  match compileFunctionNamed Compiler.Specs.ownedCounterSpec "increment" with
  | .error _ => false
  | .ok block =>
      let initWorld : Verity.ContractState :=
        { Verity.defaultState with
          storageAddr := fun i => if i = 0 then 42 else 0
          «storage» := fun i => if i = 1 then 10 else 0
          sender := 99 }
      let init : TExecState := { world := initWorld }
      match evalTBlock init block with
      | .ok _ => false
      | .revert _ => true

/-- OwnedCounter.increment by non-owner (99): reverts. -/
example : compiledOwnedCounterIncrementReverts = true := by native_decide

/-- Smoke test: all OwnedCounter spec functions compile to typed IR. -/
example : compilesOk Compiler.Specs.ownedCounterSpec "increment" = true := by native_decide
example : compilesOk Compiler.Specs.ownedCounterSpec "decrement" = true := by native_decide
example : compilesOk Compiler.Specs.ownedCounterSpec "getCount" = true := by native_decide
example : compilesOk Compiler.Specs.ownedCounterSpec "getOwner" = true := by native_decide
example : compilesOk Compiler.Specs.ownedCounterSpec "transferOwnership" = true := by native_decide

/-- End-to-end OwnedCounter.transferOwnership (happy path): owner transfers ownership, count unchanged. -/
def compiledOwnedCounterTransferOwnershipSuccess : Option (Nat × Nat) :=
  match compileFunctionNamed Compiler.Specs.ownedCounterSpec "transferOwnership" with
  | .error _ => none
  | .ok block =>
      match block.params with
      | [newOwnerParam] =>
          let initWorld : Verity.ContractState :=
            { Verity.defaultState with
              storageAddr := fun i => if i = 0 then 42 else 0
              «storage» := fun i => if i = 1 then 10 else 0
              sender := 42 }
          let init : TExecState :=
            { world := initWorld
              vars := { address := fun i =>
                          if i = newOwnerParam.id then 99 else 0 } }
          match evalTBlock init block with
          | .ok s => some ((s.world.storageAddr 0 : Nat), s.world.storage 1)
          | .revert _ => none
      | _ => none

/-- OwnedCounter.transferOwnership(newOwner=99) by owner (42): owner→99, count stays 10. -/
example : compiledOwnedCounterTransferOwnershipSuccess = some (99, 10) := by native_decide

/-- End-to-end OwnedCounter.transferOwnership (revert path): non-owner is rejected. -/
def compiledOwnedCounterTransferOwnershipReverts : Bool :=
  match compileFunctionNamed Compiler.Specs.ownedCounterSpec "transferOwnership" with
  | .error _ => false
  | .ok block =>
      match block.params with
      | [newOwnerParam] =>
          let initWorld : Verity.ContractState :=
            { Verity.defaultState with
              storageAddr := fun i => if i = 0 then 42 else 0
              «storage» := fun i => if i = 1 then 10 else 0
              sender := 77 }
          let init : TExecState :=
            { world := initWorld
              vars := { address := fun i =>
                          if i = newOwnerParam.id then 99 else 0 } }
          match evalTBlock init block with
          | .ok _ => false
          | .revert _ => true
      | _ => false

/-- OwnedCounter.transferOwnership by non-owner (77): reverts. -/
example : compiledOwnedCounterTransferOwnershipReverts = true := by native_decide

/-- Smoke test: all SimpleToken spec functions compile to typed IR. -/
example : compilesOk Compiler.Specs.simpleTokenSpec "mint" = true := by native_decide
example : compilesOk Compiler.Specs.simpleTokenSpec "transfer" = true := by native_decide
example : compilesOk Compiler.Specs.simpleTokenSpec "balanceOf" = true := by native_decide
example : compilesOk Compiler.Specs.simpleTokenSpec "totalSupply" = true := by native_decide
example : compilesOk Compiler.Specs.simpleTokenSpec "owner" = true := by native_decide

private def erc20Spec : Compiler.CompilationModel.CompilationModel :=
  Verity.Examples.MacroContracts.ERC20.spec

private def maxUint256 : Nat :=
  115792089237316195423570985008687907853269984665640564039457584007913129639935

/-- Smoke test: all ERC20 spec functions compile to typed IR. -/
example : compilesOk erc20Spec "mint" = true := by native_decide
example : compilesOk erc20Spec "transfer" = true := by native_decide
example : compilesOk erc20Spec "approve" = true := by native_decide
example : compilesOk erc20Spec "transferFrom" = true := by native_decide
example : compilesOk erc20Spec "balanceOf" = true := by native_decide
example : compilesOk erc20Spec "allowanceOf" = true := by native_decide
example : compilesOk erc20Spec "totalSupply" = true := by native_decide
example : compilesOk erc20Spec "owner" = true := by native_decide

/-- End-to-end ERC20.transferFrom (normal path): updates balances and decrements allowance. -/
def compiledERC20TransferFromSuccess : Option (Nat × Nat × Nat) :=
  match compileFunctionNamed erc20Spec "approve",
        compileFunctionNamed erc20Spec "transferFrom" with
  | .ok approveBlock, .ok transferFromBlock =>
      match approveBlock.params, transferFromBlock.params with
      | [spenderParam, approveAmountParam], [fromParam, toParam, transferAmountParam] =>
          let initWorld : Verity.ContractState :=
            { Verity.defaultState with
              storageMap := fun i addr =>
                if i == 2 && addr == 11 then 100
                else if i == 2 && addr == 33 then 50
                else 0
              sender := 11 }
          let approveInit : TExecState :=
            { world := initWorld
              vars := { address := fun i =>
                          if i = spenderParam.id then 22 else 0
                        uint256 := fun i =>
                          if i = approveAmountParam.id then 40 else 0 } }
          match evalTBlock approveInit approveBlock with
          | .revert _ => none
          | .ok postApprove =>
              let transferInit : TExecState :=
                { world := { postApprove.world with sender := 22 }
                  vars := { address := fun i =>
                              if i = fromParam.id then 11
                              else if i = toParam.id then 33
                              else 0
                            uint256 := fun i =>
                              if i = transferAmountParam.id then 30 else 0 } }
              match evalTBlock transferInit transferFromBlock with
              | .ok s =>
                  some (s.world.storageMap 2 11, s.world.storageMap 2 33, s.world.storageMap2 3 11 22)
              | .revert _ => none
      | _, _ => none
  | _, _ => none

/-- ERC20.transferFrom amount=30 after approve(40): from 100→70, to 50→80, allowance 40→10. -/
example : compiledERC20TransferFromSuccess = some (70, 80, 10) := by native_decide

/-- End-to-end ERC20.transferFrom (infinite allowance path): allowance is preserved. -/
def compiledERC20TransferFromInfiniteAllowance : Option (Nat × Nat × Nat) :=
  match compileFunctionNamed erc20Spec "transferFrom" with
  | .error _ => none
  | .ok block =>
      match block.params with
      | [fromParam, toParam, amountParam] =>
          let initWorld : Verity.ContractState :=
            { Verity.defaultState with
              storageMap := fun i addr =>
                if i == 2 && addr == 11 then 100
                else if i == 2 && addr == 33 then 50
                else 0
              storageMap2 := fun i ownerAddr spenderAddr =>
                if i == 3 && ownerAddr == 11 && spenderAddr == 22 then maxUint256 else 0
              sender := 22 }
          let init : TExecState :=
            { world := initWorld
              vars := { address := fun i =>
                          if i = fromParam.id then 11
                          else if i = toParam.id then 33
                          else 0
                        uint256 := fun i =>
                          if i = amountParam.id then 30 else 0 } }
          match evalTBlock init block with
          | .ok s => some (s.world.storageMap 2 11, s.world.storageMap 2 33, s.world.storageMap2 3 11 22)
          | .revert _ => none
      | _ => none

/-- ERC20.transferFrom with infinite allowance keeps allowance max while moving balances. -/
example : compiledERC20TransferFromInfiniteAllowance = some (70, 80, maxUint256) := by
  native_decide

/-- End-to-end ERC20.transferFrom self-transfer branch: balances unchanged, allowance decremented. -/
def compiledERC20TransferFromSelfTransfer : Option (Nat × Nat) :=
  match compileFunctionNamed erc20Spec "transferFrom" with
  | .error _ => none
  | .ok block =>
      match block.params with
      | [fromParam, toParam, amountParam] =>
          let initWorld : Verity.ContractState :=
            { Verity.defaultState with
              storageMap := fun i addr =>
                if i == 2 && addr == 11 then 100 else 0
              storageMap2 := fun i ownerAddr spenderAddr =>
                if i == 3 && ownerAddr == 11 && spenderAddr == 22 then 40 else 0
              sender := 22 }
          let init : TExecState :=
            { world := initWorld
              vars := { address := fun i =>
                          if i = fromParam.id then 11
                          else if i = toParam.id then 11
                          else 0
                        uint256 := fun i =>
                          if i = amountParam.id then 30 else 0 } }
          match evalTBlock init block with
          | .ok s => some (s.world.storageMap 2 11, s.world.storageMap2 3 11 22)
          | .revert _ => none
      | _ => none

/-- ERC20.transferFrom(from=to=11): balance stays 100 and allowance 40→10. -/
example : compiledERC20TransferFromSelfTransfer = some (100, 10) := by native_decide

/-- End-to-end ERC20.transferFrom (revert path): insufficient allowance reverts. -/
def compiledERC20TransferFromInsufficientAllowanceReverts : Bool :=
  match compileFunctionNamed erc20Spec "transferFrom" with
  | .error _ => false
  | .ok block =>
      match block.params with
      | [fromParam, toParam, amountParam] =>
          let initWorld : Verity.ContractState :=
            { Verity.defaultState with
              storageMap := fun i addr =>
                if i == 2 && addr == 11 then 100
                else if i == 2 && addr == 33 then 50
                else 0
              storageMap2 := fun i ownerAddr spenderAddr =>
                if i == 3 && ownerAddr == 11 && spenderAddr == 22 then 20 else 0
              sender := 22 }
          let init : TExecState :=
            { world := initWorld
              vars := { address := fun i =>
                          if i = fromParam.id then 11
                          else if i = toParam.id then 33
                          else 0
                        uint256 := fun i =>
                          if i = amountParam.id then 30 else 0 } }
          match evalTBlock init block with
          | .ok _ => false
          | .revert _ => true
      | _ => false

/-- ERC20.transferFrom amount=30 with allowance=20 reverts. -/
example : compiledERC20TransferFromInsufficientAllowanceReverts = true := by native_decide

private def erc721Spec : Compiler.CompilationModel.CompilationModel :=
  Verity.Examples.MacroContracts.ERC721.spec

/-- Smoke test: core ERC721 spec functions compile to typed IR. -/
example : compilesOk erc721Spec "mint" = true := by native_decide
example : compilesOk erc721Spec "transferFrom" = true := by native_decide
example : compilesOk erc721Spec "ownerOf" = true := by native_decide
example : compilesOk erc721Spec "approve" = true := by native_decide
example : compilesOk erc721Spec "getApproved" = true := by native_decide

/-- End-to-end ERC721 mint + approve + transferFrom success path. -/
def compiledERC721ApproveTransferSuccess : Option (Nat × Nat × Nat × Nat) :=
  match compileFunctionNamed erc721Spec "mint",
        compileFunctionNamed erc721Spec "approve",
        compileFunctionNamed erc721Spec "transferFrom" with
  | .ok mintBlock, .ok approveBlock, .ok transferBlock =>
      match mintBlock.params, approveBlock.params, transferBlock.params with
      | [mintToParam], [approvedParam, approveTokenParam], [fromParam, toParam, transferTokenParam] =>
          let mintInitWorld : Verity.ContractState :=
            { Verity.defaultState with
              storageAddr := fun i => if i == 0 then 9 else 0
              sender := 9 }
          let mintInit : TExecState :=
            { world := mintInitWorld
              vars := { uint256 := fun i => if i = mintToParam.id then 11 else 0 } }
          match evalTBlock mintInit mintBlock with
          | .revert _ => none
          | .ok postMint =>
              let approveInit : TExecState :=
                { world := postMint.world
                  vars := { uint256 := fun i =>
                              if i = approvedParam.id then 33
                              else if i = approveTokenParam.id then 0
                              else 0 } }
              match evalTBlock approveInit approveBlock with
              | .revert _ => none
              | .ok postApprove =>
                  let transferInit : TExecState :=
                    { world := postApprove.world
                      vars := { uint256 := fun i =>
                                  if i = fromParam.id then 11
                                  else if i = toParam.id then 33
                                  else if i = transferTokenParam.id then 0
                                  else 0 } }
                  match evalTBlock transferInit transferBlock with
                  | .revert _ => none
                  | .ok s =>
                      some (s.world.storageMapUint 3 0, s.world.storageMapUint 4 0, s.world.storage 1,
                        s.world.storage 2)
      | _, _, _ => none
  | _, _, _ => none

/-- ERC721 tokenId 0 transfers owner 11→33; approval clears; supply=1 and nextTokenId=1. -/
example : compiledERC721ApproveTransferSuccess = some (33, 0, 1, 1) := by native_decide

/-- End-to-end ERC721.transferFrom unauthorized caller reverts. -/
def compiledERC721TransferUnauthorizedReverts : Bool :=
  match compileFunctionNamed erc721Spec "mint",
        compileFunctionNamed erc721Spec "transferFrom" with
  | .ok mintBlock, .ok transferBlock =>
      match mintBlock.params, transferBlock.params with
      | [mintToParam], [fromParam, toParam, transferTokenParam] =>
          let mintInitWorld : Verity.ContractState :=
            { Verity.defaultState with
              storageAddr := fun i => if i == 0 then 9 else 0
              sender := 9 }
          let mintInit : TExecState :=
            { world := mintInitWorld
              vars := { uint256 := fun i => if i = mintToParam.id then 11 else 0 } }
          match evalTBlock mintInit mintBlock with
          | .revert _ => false
          | .ok postMint =>
              let transferInit : TExecState :=
                { world := postMint.world
                  vars := { uint256 := fun i =>
                              if i = fromParam.id then 22
                              else if i = toParam.id then 33
                              else if i = transferTokenParam.id then 0
                              else 0 } }
              match evalTBlock transferInit transferBlock with
              | .ok _ => false
              | .revert _ => true
      | _, _ => false
  | _, _ => false

/-- ERC721.transferFrom without owner/approval authorization reverts. -/
example : compiledERC721TransferUnauthorizedReverts = true := by native_decide

/-- Smoke test: all SafeCounter spec functions compile to typed IR. -/
example : compilesOk Compiler.Specs.safeCounterSpec "increment" = true := by native_decide
example : compilesOk Compiler.Specs.safeCounterSpec "decrement" = true := by native_decide
example : compilesOk Compiler.Specs.safeCounterSpec "getCount" = true := by native_decide

/-- End-to-end SafeCounter.increment (happy path): count 5 → 6. -/
def compiledSafeCounterIncrementSuccess : Option Nat :=
  match compileFunctionNamed Compiler.Specs.safeCounterSpec "increment" with
  | .error _ => none
  | .ok block =>
      let initWorld : Verity.ContractState :=
        { Verity.defaultState with «storage» := fun i => if i = 0 then 5 else 0 }
      let init : TExecState := { world := initWorld }
      match evalTBlock init block with
      | .ok s => some (s.world.storage 0)
      | .revert _ => none

/-- SafeCounter.increment(count=5): count 5→6. -/
example : compiledSafeCounterIncrementSuccess = some 6 := by native_decide

/-- End-to-end SafeCounter.decrement (happy path): count 5 → 4. -/
def compiledSafeCounterDecrementSuccess : Option Nat :=
  match compileFunctionNamed Compiler.Specs.safeCounterSpec "decrement" with
  | .error _ => none
  | .ok block =>
      let initWorld : Verity.ContractState :=
        { Verity.defaultState with «storage» := fun i => if i = 0 then 5 else 0 }
      let init : TExecState := { world := initWorld }
      match evalTBlock init block with
      | .ok s => some (s.world.storage 0)
      | .revert _ => none

/-- SafeCounter.decrement(count=5): count 5→4. -/
example : compiledSafeCounterDecrementSuccess = some 4 := by native_decide

/-- End-to-end SafeCounter.decrement (underflow): count=0 reverts. -/
def compiledSafeCounterDecrementUnderflow : Bool :=
  match compileFunctionNamed Compiler.Specs.safeCounterSpec "decrement" with
  | .error _ => false
  | .ok block =>
      let initWorld : Verity.ContractState :=
        { Verity.defaultState with «storage» := fun _ => 0 }
      let init : TExecState := { world := initWorld }
      match evalTBlock init block with
      | .ok _ => false
      | .revert _ => true

/-- SafeCounter.decrement(count=0): reverts with "Underflow in decrement". -/
example : compiledSafeCounterDecrementUnderflow = true := by native_decide

/-- End-to-end SafeCounter.getCount: returns stored count via lowered pipeline. -/
def compiledSafeCounterGetCountReturn : Option Nat :=
  match compileFunctionNamed Compiler.Specs.safeCounterSpec "getCount" with
  | .error _ => none
  | .ok block =>
      let initWorld : Verity.ContractState :=
        { Verity.defaultState with «storage» := fun i => if i = 0 then 42 else 0 }
      let init : TExecState := { world := initWorld }
      execLoweredReturn 256 (mkIRStateFromTyped init block) block

/-- SafeCounter.getCount returns stored count (42) through the full pipeline. -/
example : compiledSafeCounterGetCountReturn = some 42 := by native_decide

/-- Compiler correctness base lemma: list compilation composes by append. -/
example (fields : List Compiler.CompilationModel.Field)
    (pre post : List Compiler.CompilationModel.Stmt) :
    compileStmts fields (pre ++ post) = (do
      compileStmts fields pre
      compileStmts fields post) :=
  compileStmts_append fields pre post

example (fields : List Compiler.CompilationModel.Field)
    (pre post : List Compiler.CompilationModel.Stmt)
    (st : CompileState) :
    (compileStmts fields (pre ++ post)).run st =
      ((do
          compileStmts fields pre
          compileStmts fields post).run st) :=
  compileStmts_append_from fields pre post st

example (fields : List Compiler.CompilationModel.Field)
    (fieldName : String) (slotIdx : Nat)
    (init : TExecState) (n : Nat)
    (hfind : Compiler.CompilationModel.findFieldWithResolvedSlot fields fieldName =
      some (({ name := fieldName, ty := Compiler.CompilationModel.FieldType.uint256 } : Compiler.CompilationModel.Field), slotIdx)) :
    execCompiledSetStorageLiteral fields fieldName init n =
      .ok { init with world := execSourceSetStorageLiteral init.world slotIdx n } :=
  compile_setStorage_literal_semantics fields fieldName slotIdx init n hfind

example (fields : List Compiler.CompilationModel.Field)
    (fieldName tmp : String) (slotIdx : Nat)
    (init : TExecState) (n : Nat)
    (hfind : Compiler.CompilationModel.findFieldWithResolvedSlot fields fieldName =
      some (({ name := fieldName, ty := Compiler.CompilationModel.FieldType.uint256 } : Compiler.CompilationModel.Field), slotIdx)) :
    execCompiledLetSetStorageLocalLiteral fields fieldName tmp init n =
      .ok
        ({ init with
            world := execSourceSetStorageLiteral init.world slotIdx n
            vars := init.vars.set { id := 0, ty := Ty.uint256 } (n : Verity.Core.Uint256) }) :=
  compile_let_setStorage_local_literal_semantics fields fieldName tmp slotIdx init n hfind

example (fields : List Compiler.CompilationModel.Field)
    (fieldName tmp : String) (slotIdx : Nat)
    (init : TExecState) (n m : Nat)
    (hfind : Compiler.CompilationModel.findFieldWithResolvedSlot fields fieldName =
      some (({ name := fieldName, ty := Compiler.CompilationModel.FieldType.uint256 } : Compiler.CompilationModel.Field), slotIdx)) :
    execCompiledLetAssignSetStorageLocalLiteral fields fieldName tmp init n m =
      .ok
        ({ init with
            world := execSourceSetStorageLiteral init.world slotIdx m
            vars := TVars.set
              (TVars.set init.vars { id := 0, ty := Ty.uint256 } (n : Verity.Core.Uint256))
              { id := 1, ty := Ty.uint256 } (m : Verity.Core.Uint256) }) :=
  compile_let_assign_setStorage_local_literal_semantics fields fieldName tmp slotIdx init n m hfind

example (fields : List Compiler.CompilationModel.Field)
    (fieldName tmp : String) (slotIdx : Nat)
    (init : TExecState) (n m : Nat)
    (hfind : Compiler.CompilationModel.findFieldWithResolvedSlot fields fieldName =
      some (({ name := fieldName, ty := Compiler.CompilationModel.FieldType.uint256 } : Compiler.CompilationModel.Field), slotIdx)) :
    execCompiledLetAssignAddSetStorageLocalLiteral fields fieldName tmp init n m =
      .ok
        ({ init with
            world := execSourceSetStorageLiteral init.world slotIdx
              ((n : Verity.Core.Uint256).add (m : Verity.Core.Uint256))
            vars := TVars.set
              (TVars.set init.vars { id := 0, ty := Ty.uint256 } (n : Verity.Core.Uint256))
              { id := 1, ty := Ty.uint256 }
                ((n : Verity.Core.Uint256).add (m : Verity.Core.Uint256)) }) :=
  compile_let_assign_add_setStorage_local_literal_semantics
    fields fieldName tmp slotIdx init n m hfind

example (fields : List Compiler.CompilationModel.Field)
    (fieldName tmp : String) (slotIdx : Nat)
    (init : TExecState) (n m : Nat)
    (hfind : Compiler.CompilationModel.findFieldWithResolvedSlot fields fieldName =
      some (({ name := fieldName, ty := Compiler.CompilationModel.FieldType.uint256 } : Compiler.CompilationModel.Field), slotIdx)) :
    execCompiledLetAssignSubSetStorageLocalLiteral fields fieldName tmp init n m =
      .ok
        ({ init with
            world := execSourceSetStorageLiteral init.world slotIdx
              ((n : Verity.Core.Uint256).sub (m : Verity.Core.Uint256))
            vars := TVars.set
              (TVars.set init.vars { id := 0, ty := Ty.uint256 } (n : Verity.Core.Uint256))
              { id := 1, ty := Ty.uint256 }
                ((n : Verity.Core.Uint256).sub (m : Verity.Core.Uint256)) }) :=
  compile_let_assign_sub_setStorage_local_literal_semantics
    fields fieldName tmp slotIdx init n m hfind

example (fields : List Compiler.CompilationModel.Field)
    (fieldName tmp : String) (slotIdx : Nat)
    (init : TExecState) (n m : Nat)
    (hfind : Compiler.CompilationModel.findFieldWithResolvedSlot fields fieldName =
      some (({ name := fieldName, ty := Compiler.CompilationModel.FieldType.uint256 } : Compiler.CompilationModel.Field), slotIdx)) :
    execCompiledLetAssignMulSetStorageLocalLiteral fields fieldName tmp init n m =
      .ok
        ({ init with
            world := execSourceSetStorageLiteral init.world slotIdx
              ((n : Verity.Core.Uint256).mul (m : Verity.Core.Uint256))
            vars := TVars.set
              (TVars.set init.vars { id := 0, ty := Ty.uint256 } (n : Verity.Core.Uint256))
              { id := 1, ty := Ty.uint256 }
                ((n : Verity.Core.Uint256).mul (m : Verity.Core.Uint256)) }) :=
  compile_let_assign_mul_setStorage_local_literal_semantics
    fields fieldName tmp slotIdx init n m hfind

example (fields : List Compiler.CompilationModel.Field)
    (init : TExecState) (n : Nat) :
    execCompiledReturnLiteral fields init n = execSourceReturnLiteral init n :=
  compile_return_literal_semantics fields init n

example (fields : List Compiler.CompilationModel.Field)
    (tmp : String) (init : TExecState) (n : Nat) :
    execCompiledLetReturnLocalLiteral fields tmp init n =
      execSourceLetReturnLocalLiteral init n :=
  compile_let_return_local_literal_semantics fields tmp init n

example (fields : List Compiler.CompilationModel.Field)
    (fieldName : String) (slotIdx : Nat)
    (init : TExecState) (n m thenVal elseVal : Nat)
    (hfind : Compiler.CompilationModel.findFieldWithResolvedSlot fields fieldName =
      some (({ name := fieldName, ty := Compiler.CompilationModel.FieldType.uint256 } : Compiler.CompilationModel.Field), slotIdx)) :
    execCompiledIteEqSetStorageLiterals fields fieldName init n m thenVal elseVal =
      .ok { init with world := execSourceIteEqSetStorageLiterals init.world slotIdx n m thenVal elseVal } :=
  compile_ite_eq_setStorage_literals_semantics
    fields fieldName slotIdx init n m thenVal elseVal hfind

example (fields : List Compiler.CompilationModel.Field)
    (init : TExecState) (n m : Nat) (message : String) :
    execCompiledRequireEqLiterals fields init n m message =
      execSourceRequireEqLiterals init n m message :=
  compile_require_eq_literals_semantics fields init n m message

example (fields : List Compiler.CompilationModel.Field)
    (init : TExecState) (n m : Nat) (message : String) :
    execCompiledRequireNotEqLiterals fields init n m message =
      execSourceRequireNotEqLiterals init n m message :=
  compile_require_not_eq_literals_semantics fields init n m message

example (fields : List Compiler.CompilationModel.Field)
    (init : TExecState) (n m : Nat) (message : String) :
    execCompiledRequireLtLiterals fields init n m message =
      execSourceRequireLtLiterals init n m message :=
  compile_require_lt_literals_semantics fields init n m message

example (fields : List Compiler.CompilationModel.Field)
    (init : TExecState) (n m : Nat) (message : String) :
    execCompiledRequireGtLiterals fields init n m message =
      execSourceRequireGtLiterals init n m message :=
  compile_require_gt_literals_semantics fields init n m message

example (fields : List Compiler.CompilationModel.Field)
    (init : TExecState) (n m : Nat) (message : String) :
    execCompiledRequireGeLiterals fields init n m message =
      execSourceRequireGeLiterals init n m message :=
  compile_require_ge_literals_semantics fields init n m message

example (fields : List Compiler.CompilationModel.Field)
    (init : TExecState) (n m : Nat) (message : String) :
    execCompiledRequireLeLiterals fields init n m message =
      execSourceRequireLeLiterals init n m message :=
  compile_require_le_literals_semantics fields init n m message

example (guard : RequireBinaryLiteralGuard)
    (fields : List Compiler.CompilationModel.Field)
    (init : TExecState) (n m : Nat) (message : String) :
    execCompiledRequireBinaryLiteralGuard guard fields init n m message =
      execSourceRequireBinaryLiteralGuard guard init n m message :=
  compile_require_binary_literal_guard_semantics guard fields init n m message

example (fields : List Compiler.CompilationModel.Field)
    (init : TExecState) (clauses : List RequireBinaryLiteralClause) :
    execCompiledRequireBinaryLiteralClauses fields init clauses =
      execSourceRequireBinaryLiteralClauses init clauses :=
  compile_require_binary_literal_clauses_semantics fields init clauses

example (fields : List Compiler.CompilationModel.Field)
    (init : TExecState) (n m p q : Nat) (message : String) :
    execCompiledRequireAndEqLtLiterals fields init n m p q message =
      execSourceRequireAndEqLtLiterals init n m p q message :=
  compile_require_and_eq_lt_literals_semantics fields init n m p q message

example (fields : List Compiler.CompilationModel.Field)
    (init : TExecState) (n m p q : Nat) (message : String) :
    execCompiledRequireOrEqLtLiterals fields init n m p q message =
      execSourceRequireOrEqLtLiterals init n m p q message :=
  compile_require_or_eq_lt_literals_semantics fields init n m p q message

example (family : RequireLiteralGuardFamily)
    (fields : List Compiler.CompilationModel.Field)
    (init : TExecState) (n m p q : Nat) (message : String) :
    execCompiledRequireLiteralGuardFamily family fields init n m p q message =
      execSourceRequireLiteralGuardFamily family init n m p q message :=
  compile_require_literal_guard_family_semantics family fields init n m p q message

example (fields : List Compiler.CompilationModel.Field)
    (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) :
    execCompiledRequireLiteralGuardFamilyClauses fields init clauses =
      execSourceRequireLiteralGuardFamilyClauses init clauses :=
  compile_require_literal_guard_family_clauses_semantics fields init clauses

example (fields : List Compiler.CompilationModel.Field)
    (fieldName : String) (slotIdx : Nat) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) (writeVal : Nat)
    (hfind : Compiler.CompilationModel.findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := Compiler.CompilationModel.FieldType.uint256 }, slotIdx)) :
    execCompiledRequireFamilyClausesThenSetStorageLiteral
        fields fieldName init clauses writeVal =
      execSourceRequireFamilyClausesThenSetStorageLiteral
        init clauses slotIdx writeVal :=
  compile_require_family_clauses_then_setStorage_literal_semantics
    fields fieldName slotIdx init clauses writeVal hfind

example (fields : List Compiler.CompilationModel.Field)
    (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) (retVal : Nat) :
    execCompiledRequireFamilyClausesThenReturnLiteral
        fields init clauses retVal =
      execSourceRequireFamilyClausesThenReturnLiteral
        init clauses retVal :=
  compile_require_family_clauses_then_return_literal_semantics
    fields init clauses retVal

example (fields : List Compiler.CompilationModel.Field)
    (tmp : String) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) (retVal : Nat) :
    execCompiledRequireFamilyClausesThenLetReturnLocalLiteral
        fields tmp init clauses retVal =
      execSourceRequireFamilyClausesThenLetReturnLocalLiteral
        init clauses retVal :=
  compile_require_family_clauses_then_let_return_local_literal_semantics
    fields tmp init clauses retVal

example (fields : List Compiler.CompilationModel.Field)
    (fieldName tmp : String) (slotIdx : Nat) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) (n : Nat)
    (hfind : Compiler.CompilationModel.findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := Compiler.CompilationModel.FieldType.uint256 }, slotIdx)) :
    execCompiledRequireFamilyClausesThenLetSetStorageLocalLiteral
        fields fieldName tmp init clauses n =
      execSourceRequireFamilyClausesThenLetSetStorageLocalLiteral
        init clauses slotIdx n :=
  compile_require_family_clauses_then_let_setStorage_local_literal_semantics
    fields fieldName tmp slotIdx init clauses n hfind

example (fields : List Compiler.CompilationModel.Field)
    (fieldName tmp : String) (slotIdx : Nat) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) (n m : Nat)
    (hfind : Compiler.CompilationModel.findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := Compiler.CompilationModel.FieldType.uint256 }, slotIdx)) :
    execCompiledRequireFamilyClausesThenLetAssignSetStorageLocalLiteral
        fields fieldName tmp init clauses n m =
      execSourceRequireFamilyClausesThenLetAssignSetStorageLocalLiteral
        init clauses slotIdx n m :=
  compile_require_family_clauses_then_let_assign_setStorage_local_literal_semantics
    fields fieldName tmp slotIdx init clauses n m hfind

example (fields : List Compiler.CompilationModel.Field)
    (fieldName tmp : String) (slotIdx : Nat) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) (n m : Nat)
    (hfind : Compiler.CompilationModel.findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := Compiler.CompilationModel.FieldType.uint256 }, slotIdx)) :
    execCompiledRequireFamilyClausesThenLetAssignAddSetStorageLocalLiteral
        fields fieldName tmp init clauses n m =
      execSourceRequireFamilyClausesThenLetAssignAddSetStorageLocalLiteral
        init clauses slotIdx n m :=
  compile_require_family_clauses_then_let_assign_add_setStorage_local_literal_semantics
    fields fieldName tmp slotIdx init clauses n m hfind

example (fields : List Compiler.CompilationModel.Field)
    (fieldName tmp : String) (slotIdx : Nat) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) (n m : Nat)
    (hfind : Compiler.CompilationModel.findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := Compiler.CompilationModel.FieldType.uint256 }, slotIdx)) :
    execCompiledRequireFamilyClausesThenLetAssignSubSetStorageLocalLiteral
        fields fieldName tmp init clauses n m =
      execSourceRequireFamilyClausesThenLetAssignSubSetStorageLocalLiteral
        init clauses slotIdx n m :=
  compile_require_family_clauses_then_let_assign_sub_setStorage_local_literal_semantics
    fields fieldName tmp slotIdx init clauses n m hfind

example (fields : List Compiler.CompilationModel.Field)
    (fieldName tmp : String) (slotIdx : Nat) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) (n m : Nat)
    (hfind : Compiler.CompilationModel.findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := Compiler.CompilationModel.FieldType.uint256 }, slotIdx)) :
    execCompiledRequireFamilyClausesThenLetAssignMulSetStorageLocalLiteral
        fields fieldName tmp init clauses n m =
      execSourceRequireFamilyClausesThenLetAssignMulSetStorageLocalLiteral
        init clauses slotIdx n m :=
  compile_require_family_clauses_then_let_assign_mul_setStorage_local_literal_semantics
    fields fieldName tmp slotIdx init clauses n m hfind

example (family : RequireLiteralGuardFamily)
    (fields : List Compiler.CompilationModel.Field)
    (fieldName : String) (slotIdx : Nat) (init : TExecState)
    (n m p q : Nat) (message : String) (writeVal : Nat)
    (hfind : Compiler.CompilationModel.findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := Compiler.CompilationModel.FieldType.uint256 }, slotIdx)) :
    execCompiledRequireFamilyThenSetStorageLiteral
        family fields fieldName init n m p q message writeVal =
      execSourceRequireFamilyThenSetStorageLiteral
        family init slotIdx n m p q message writeVal :=
  compile_require_family_then_setStorage_literal_semantics
    family fields fieldName slotIdx init n m p q message writeVal hfind

example (family : RequireLiteralGuardFamily)
    (fields : List Compiler.CompilationModel.Field)
    (init : TExecState)
    (n m p q : Nat) (message : String) (retVal : Nat) :
    execCompiledRequireFamilyThenReturnLiteral
        family fields init n m p q message retVal =
      execSourceRequireFamilyThenReturnLiteral
        family init n m p q message retVal :=
  compile_require_family_then_return_literal_semantics
    family fields init n m p q message retVal

example (fields : List Compiler.CompilationModel.Field)
    (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) :
    execCompiledRequireFamilyClausesThenNoop fields init clauses =
      execSourceRequireFamilyClausesThenNoop init clauses :=
  compile_require_family_clauses_then_noop_semantics fields init clauses

example (fields : List Compiler.CompilationModel.Field)
    (fieldName : String) (slotIdx : Nat) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m thenVal elseVal : Nat)
    (hfind : Compiler.CompilationModel.findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := Compiler.CompilationModel.FieldType.uint256 }, slotIdx)) :
    execCompiledRequireFamilyClausesThenIteEqSetStorageLiterals
        fields fieldName init clauses n m thenVal elseVal =
      execSourceRequireFamilyClausesThenIteEqSetStorageLiterals
        init clauses slotIdx n m thenVal elseVal :=
  compile_require_family_clauses_then_ite_eq_setStorage_literals_semantics
    fields fieldName slotIdx init clauses n m thenVal elseVal hfind

example (fields : List Compiler.CompilationModel.Field)
    (fieldName : String) (slotIdx : Nat) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m thenVal elseVal : Nat)
    (hfind : Compiler.CompilationModel.findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := Compiler.CompilationModel.FieldType.uint256 }, slotIdx)) :
    execCompiledRequireFamilyClausesThenIteEqSetStorageThenReturnLiteral
        fields fieldName init clauses n m thenVal elseVal =
      execSourceRequireFamilyClausesThenIteEqSetStorageThenReturnLiteral
        init clauses slotIdx n m thenVal elseVal :=
  compile_require_family_clauses_then_ite_eq_setStorage_then_return_literal_semantics
    fields fieldName slotIdx init clauses n m thenVal elseVal hfind

example (fields : List Compiler.CompilationModel.Field)
    (fieldName : String) (slotIdx : Nat) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m thenVal elseVal : Nat)
    (hfind : Compiler.CompilationModel.findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := Compiler.CompilationModel.FieldType.uint256 }, slotIdx)) :
    execCompiledRequireFamilyClausesThenIteEqReturnThenSetStorageLiteral
        fields fieldName init clauses n m thenVal elseVal =
      execSourceRequireFamilyClausesThenIteEqReturnThenSetStorageLiteral
        init clauses slotIdx n m thenVal elseVal :=
  compile_require_family_clauses_then_ite_eq_return_then_setStorage_literal_semantics
    fields fieldName slotIdx init clauses n m thenVal elseVal hfind

example (fields : List Compiler.CompilationModel.Field)
    (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m thenVal elseVal : Nat) :
    execCompiledRequireFamilyClausesThenIteEqReturnLiterals
        fields init clauses n m thenVal elseVal =
      execSourceRequireFamilyClausesThenIteEqReturnLiterals
        init clauses n m thenVal elseVal :=
  compile_require_family_clauses_then_ite_eq_return_literals_semantics
    fields init clauses n m thenVal elseVal

example (fields : List Compiler.CompilationModel.Field)
    (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m p q thenVal elseVal outerElseVal : Nat) :
    execCompiledRequireFamilyClausesThenIteEqThenIteEqReturnLiterals
        fields init clauses n m p q thenVal elseVal outerElseVal =
      execSourceRequireFamilyClausesThenIteEqThenIteEqReturnLiterals
        init clauses n m p q thenVal elseVal outerElseVal :=
  compile_require_family_clauses_then_ite_eq_then_ite_eq_return_literals_semantics
    fields init clauses n m p q thenVal elseVal outerElseVal

example (fields : List Compiler.CompilationModel.Field)
    (fieldName : String) (slotIdx : Nat) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m p q thenVal elseVal outerElseVal : Nat)
    (hfind : Compiler.CompilationModel.findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := Compiler.CompilationModel.FieldType.uint256 }, slotIdx)) :
    execCompiledRequireFamilyClausesThenIteEqThenIteEqSetStorageLiteralsThenReturnLiteral
        fields fieldName init clauses n m p q thenVal elseVal outerElseVal =
      execSourceRequireFamilyClausesThenIteEqThenIteEqSetStorageLiteralsThenReturnLiteral
        init clauses slotIdx n m p q thenVal elseVal outerElseVal :=
  compile_require_family_clauses_then_ite_eq_then_ite_eq_setStorage_literals_then_return_literal_semantics
    fields fieldName slotIdx init clauses n m p q thenVal elseVal outerElseVal hfind

example (fields : List Compiler.CompilationModel.Field)
    (fieldName : String) (slotIdx : Nat) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m p q thenVal elseVal outerElseVal : Nat)
    (hfind : Compiler.CompilationModel.findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := Compiler.CompilationModel.FieldType.uint256 }, slotIdx)) :
    execCompiledRequireFamilyClausesThenIteEqThenIteEqReturnLiteralsThenSetStorageLiteral
        fields fieldName init clauses n m p q thenVal elseVal outerElseVal =
      execSourceRequireFamilyClausesThenIteEqThenIteEqReturnLiteralsThenSetStorageLiteral
        init clauses slotIdx n m p q thenVal elseVal outerElseVal :=
  compile_require_family_clauses_then_ite_eq_then_ite_eq_return_literals_then_setStorage_literal_semantics
    fields fieldName slotIdx init clauses n m p q thenVal elseVal outerElseVal hfind

example (fields : List Compiler.CompilationModel.Field)
    (fieldName : String) (slotIdx : Nat) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m p q thenVal elseVal outerElseWriteVal outerElseRetVal : Nat)
    (hfind : Compiler.CompilationModel.findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := Compiler.CompilationModel.FieldType.uint256 }, slotIdx)) :
    execCompiledRequireFamilyClausesThenIteEqThenIteEqReturnLiteralsThenSetStorageLiteralThenReturnLiteral
        fields fieldName init clauses n m p q thenVal elseVal outerElseWriteVal outerElseRetVal =
      execSourceRequireFamilyClausesThenIteEqThenIteEqReturnLiteralsThenSetStorageLiteralThenReturnLiteral
        init clauses slotIdx n m p q thenVal elseVal outerElseWriteVal outerElseRetVal :=
  compile_require_family_clauses_then_ite_eq_then_ite_eq_return_literals_then_setStorage_literal_then_return_literal_semantics
    fields fieldName slotIdx init clauses n m p q thenVal elseVal outerElseWriteVal outerElseRetVal hfind

example (fields : List Compiler.CompilationModel.Field)
    (fieldName : String) (slotIdx : Nat) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m p q thenVal elseVal outerElseVal : Nat)
    (hfind : Compiler.CompilationModel.findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := Compiler.CompilationModel.FieldType.uint256 }, slotIdx)) :
    execCompiledRequireFamilyClausesThenIteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral
        fields fieldName init clauses n m p q thenVal elseVal outerElseVal =
      execSourceRequireFamilyClausesThenIteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral
        init clauses slotIdx n m p q thenVal elseVal outerElseVal :=
  compile_require_family_clauses_then_ite_eq_then_ite_eq_setStorage_literals_then_setStorage_literal_semantics
    fields fieldName slotIdx init clauses n m p q thenVal elseVal outerElseVal hfind

example (fields : List Compiler.CompilationModel.Field)
    (fieldName : String) (slotIdx : Nat) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m p q thenVal elseVal outerElseVal : Nat)
    (hfind : Compiler.CompilationModel.findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := Compiler.CompilationModel.FieldType.uint256 }, slotIdx)) :
    execCompiledRequireFamilyClausesThenIteEqThenIteEqSetStorageThenReturnLiteralThenReturnLiteral
        fields fieldName init clauses n m p q thenVal elseVal outerElseVal =
      execSourceRequireFamilyClausesThenIteEqThenIteEqSetStorageThenReturnLiteralThenReturnLiteral
        init clauses slotIdx n m p q thenVal elseVal outerElseVal :=
  compile_require_family_clauses_then_ite_eq_then_ite_eq_setStorage_then_return_literal_then_return_literal_semantics
    fields fieldName slotIdx init clauses n m p q thenVal elseVal outerElseVal hfind

example (fields : List Compiler.CompilationModel.Field)
    (fieldName : String) (slotIdx : Nat) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m p q thenVal elseVal outerElseVal : Nat)
    (hfind : Compiler.CompilationModel.findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := Compiler.CompilationModel.FieldType.uint256 }, slotIdx)) :
    execCompiledRequireFamilyClausesThenIteEqThenIteEqSetStorageThenReturnLiteralThenSetStorageLiteral
        fields fieldName init clauses n m p q thenVal elseVal outerElseVal =
      execSourceRequireFamilyClausesThenIteEqThenIteEqSetStorageThenReturnLiteralThenSetStorageLiteral
        init clauses slotIdx n m p q thenVal elseVal outerElseVal :=
  compile_require_family_clauses_then_ite_eq_then_ite_eq_setStorage_then_return_literal_then_setStorage_literal_semantics
    fields fieldName slotIdx init clauses n m p q thenVal elseVal outerElseVal hfind

example (fields : List Compiler.CompilationModel.Field)
    (fieldName : String) (slotIdx : Nat) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m p q thenVal elseVal outerElseVal : Nat)
    (hfind : Compiler.CompilationModel.findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := Compiler.CompilationModel.FieldType.uint256 }, slotIdx)) :
    execCompiledRequireFamilyClausesThenIteEqThenIteEqReturnThenSetStorageLiteralThenReturnLiteral
        fields fieldName init clauses n m p q thenVal elseVal outerElseVal =
      execSourceRequireFamilyClausesThenIteEqThenIteEqReturnThenSetStorageLiteralThenReturnLiteral
        init clauses slotIdx n m p q thenVal elseVal outerElseVal :=
  compile_require_family_clauses_then_ite_eq_then_ite_eq_return_then_setStorage_literal_then_return_literal_semantics
    fields fieldName slotIdx init clauses n m p q thenVal elseVal outerElseVal hfind

example (fields : List Compiler.CompilationModel.Field)
    (fieldName : String) (slotIdx : Nat) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m p q thenVal elseVal outerElseVal : Nat)
    (hfind : Compiler.CompilationModel.findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := Compiler.CompilationModel.FieldType.uint256 }, slotIdx)) :
    execCompiledRequireFamilyClausesThenIteEqThenIteEqReturnThenSetStorageLiteralThenSetStorageLiteral
        fields fieldName init clauses n m p q thenVal elseVal outerElseVal =
      execSourceRequireFamilyClausesThenIteEqThenIteEqReturnThenSetStorageLiteralThenSetStorageLiteral
        init clauses slotIdx n m p q thenVal elseVal outerElseVal :=
  compile_require_family_clauses_then_ite_eq_then_ite_eq_return_then_setStorage_literal_then_setStorage_literal_semantics
    fields fieldName slotIdx init clauses n m p q thenVal elseVal outerElseVal hfind

example (fields : List Compiler.CompilationModel.Field)
    (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (tail : RequireFamilyClausesTail fields) :
    execCompiledRequireFamilyClausesThenTail fields init clauses tail =
      execSourceRequireFamilyClausesThenTail fields init clauses tail :=
  compile_require_family_clauses_then_tail_semantics fields init clauses tail

example (fields : List Compiler.CompilationModel.Field)
    (init : TExecState)
    (programs : List (RequireFamilyClausesTailProgram fields)) :
    execCompiledRequireFamilyClausesTailPrograms fields init programs =
      execSourceRequireFamilyClausesTailPrograms fields init programs :=
  compile_require_family_clauses_tail_programs_semantics fields init programs

example (fields : List Compiler.CompilationModel.Field)
    (init : TExecState)
    (pre post : List (RequireFamilyClausesTailProgram fields)) :
    execCompiledRequireFamilyClausesTailPrograms fields init (pre ++ post) =
      execSourceRequireFamilyClausesTailPrograms fields init (pre ++ post) :=
  compile_require_family_clauses_tail_programs_append_semantics fields init pre post

example (fields : List Compiler.CompilationModel.Field)
    (init : TExecState)
    (fragments : List (SupportedStmtFragment fields)) :
    execCompiledSupportedStmtFragments fields init fragments =
      execSourceSupportedStmtFragments fields init fragments :=
  compile_supported_stmt_fragments_semantics fields init fragments

example (fields : List Compiler.CompilationModel.Field)
    (init : TExecState)
    (stmts : List Compiler.CompilationModel.Stmt)
    (hSupported : SupportedStmtList fields stmts) :
    ∃ fragments : List (SupportedStmtFragment fields),
      supportedStmtFragmentsToStmts fragments = stmts ∧
      execCompiledSupportedStmtFragments fields init fragments =
        execSourceSupportedStmtFragments fields init fragments :=
  compile_supported_stmt_list_semantics fields init stmts hSupported

example (fields : List Compiler.CompilationModel.Field)
    (init : TExecState)
    (stmts : List Compiler.CompilationModel.Stmt)
    (hSupported : SupportedStmtList fields stmts) :
    execCompiledSupportedStmtList fields init stmts hSupported =
      execSourceSupportedStmtList fields init stmts hSupported :=
  compile_supported_stmt_list_direct_semantics fields init stmts hSupported

open Compiler.CompilationModel in
/-- Counter.increment body belongs to the supported fragment. -/
example : SupportedStmtList counterFields
    [ Stmt.letVar "current" (Expr.storage "count")
    , Stmt.setStorage "count" (Expr.add (Expr.localVar "current") (Expr.literal 1))
    , Stmt.stop ] :=
  counter_increment_supported

open Compiler.CompilationModel in
/-- Counter.decrement body belongs to the supported fragment. -/
example : SupportedStmtList counterFields
    [ Stmt.letVar "current" (Expr.storage "count")
    , Stmt.setStorage "count" (Expr.sub (Expr.localVar "current") (Expr.literal 1))
    , Stmt.stop ] :=
  counter_decrement_supported

open Compiler.CompilationModel in
/-- Counter.getCount body belongs to the supported fragment. -/
example : SupportedStmtList counterFields
    [ Stmt.letVar "current" (Expr.storage "count")
    , Stmt.return (Expr.localVar "current") ] :=
  counter_getCount_supported

open Compiler.CompilationModel in
/-- Counter.increment compilation correctness follows from the generic theorem. -/
example (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment counterFields),
      supportedStmtFragmentsToStmts fragments =
        [ Stmt.letVar "current" (Expr.storage "count")
        , Stmt.setStorage "count" (Expr.add (Expr.localVar "current") (Expr.literal 1))
        , Stmt.stop ] ∧
      execCompiledSupportedStmtFragments counterFields init fragments =
        execSourceSupportedStmtFragments counterFields init fragments :=
  counter_increment_correctness init

open Compiler.CompilationModel in
/-- Counter.decrement compilation correctness follows from the generic theorem. -/
example (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment counterFields),
      supportedStmtFragmentsToStmts fragments =
        [ Stmt.letVar "current" (Expr.storage "count")
        , Stmt.setStorage "count" (Expr.sub (Expr.localVar "current") (Expr.literal 1))
        , Stmt.stop ] ∧
      execCompiledSupportedStmtFragments counterFields init fragments =
        execSourceSupportedStmtFragments counterFields init fragments :=
  counter_decrement_correctness init

open Compiler.CompilationModel in
/-- Counter.getCount compilation correctness follows from the generic theorem. -/
example (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment counterFields),
      supportedStmtFragmentsToStmts fragments =
        [ Stmt.letVar "current" (Expr.storage "count")
        , Stmt.return (Expr.localVar "current") ] ∧
      execCompiledSupportedStmtFragments counterFields init fragments =
        execSourceSupportedStmtFragments counterFields init fragments :=
  counter_getCount_correctness init

open Compiler.CompilationModel in
/-- SimpleStorage.retrieve compilation correctness follows from the generic theorem. -/
example (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment simpleStorageFields),
      supportedStmtFragmentsToStmts fragments =
        [Stmt.return (Expr.storage "storedData")] ∧
      execCompiledSupportedStmtFragments simpleStorageFields init fragments =
        execSourceSupportedStmtFragments simpleStorageFields init fragments :=
  simpleStorage_retrieve_correctness init

open Compiler.CompilationModel in
/-- Owned.getOwner compilation correctness follows from the generic theorem. -/
example (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment ownedFields),
      supportedStmtFragmentsToStmts fragments =
        [Stmt.return (Expr.storage "owner")] ∧
      execCompiledSupportedStmtFragments ownedFields init fragments =
        execSourceSupportedStmtFragments ownedFields init fragments :=
  owned_getOwner_correctness init

open Compiler.CompilationModel in
/-- SafeCounter.getCount compilation correctness follows from the generic theorem. -/
example (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment safeCounterFields),
      supportedStmtFragmentsToStmts fragments =
        [Stmt.return (Expr.storage "count")] ∧
      execCompiledSupportedStmtFragments safeCounterFields init fragments =
        execSourceSupportedStmtFragments safeCounterFields init fragments :=
  safeCounter_getCount_correctness init

open Compiler.CompilationModel in
/-- OwnedCounter.getCount compilation correctness follows from the generic theorem. -/
example (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment ownedCounterFields),
      supportedStmtFragmentsToStmts fragments =
        [Stmt.return (Expr.storage "count")] ∧
      execCompiledSupportedStmtFragments ownedCounterFields init fragments =
        execSourceSupportedStmtFragments ownedCounterFields init fragments :=
  ownedCounter_getCount_correctness init

open Compiler.CompilationModel in
/-- OwnedCounter.getOwner compilation correctness follows from the generic theorem. -/
example (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment ownedCounterFields),
      supportedStmtFragmentsToStmts fragments =
        [Stmt.return (Expr.storage "owner")] ∧
      execCompiledSupportedStmtFragments ownedCounterFields init fragments =
        execSourceSupportedStmtFragments ownedCounterFields init fragments :=
  ownedCounter_getOwner_correctness init

open Compiler.CompilationModel in
/-- OwnedCounter.increment compilation correctness follows from the generic theorem. -/
example (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment ownedCounterFields),
      supportedStmtFragmentsToStmts fragments =
        [ Stmt.require (Expr.eq Expr.caller (Expr.storage "owner")) "Not owner"
        , Stmt.setStorage "count" (Expr.add (Expr.storage "count") (Expr.literal 1))
        , Stmt.stop ] ∧
      execCompiledSupportedStmtFragments ownedCounterFields init fragments =
        execSourceSupportedStmtFragments ownedCounterFields init fragments :=
  ownedCounter_increment_correctness init

open Compiler.CompilationModel in
/-- OwnedCounter.decrement compilation correctness follows from the generic theorem. -/
example (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment ownedCounterFields),
      supportedStmtFragmentsToStmts fragments =
        [ Stmt.require (Expr.eq Expr.caller (Expr.storage "owner")) "Not owner"
        , Stmt.setStorage "count" (Expr.sub (Expr.storage "count") (Expr.literal 1))
        , Stmt.stop ] ∧
      execCompiledSupportedStmtFragments ownedCounterFields init fragments =
        execSourceSupportedStmtFragments ownedCounterFields init fragments :=
  ownedCounter_decrement_correctness init

-- ============================================================================
-- Mapping return pattern tests (item 3.5)
-- ============================================================================

/-- End-to-end Ledger.getBalance: compiled block preserves state (return is read-only). -/
def compiledLedgerGetBalancePreservesState : Bool :=
  match compileFunctionNamed Compiler.Specs.ledgerSpec "getBalance" with
  | .error _ => false
  | .ok block =>
      match block.params with
      | [addrParam] =>
          let initWorld : Verity.ContractState :=
            { Verity.defaultState with
              storageMap := fun i addr =>
                if i == 0 && addr == 42 then 200 else 0 }
          let init : TExecState :=
            { world := initWorld
              vars := { address := fun i =>
                          if i = addrParam.id then 42 else 0 } }
          match evalTBlock init block with
          | .ok _ => true
          | .revert _ => false
      | _ => false

/-- Ledger.getBalance(addr=42): succeeds without reverting. -/
example : compiledLedgerGetBalancePreservesState = true := by native_decide

/-- End-to-end SimpleToken.balanceOf: compiled block preserves state (return is read-only). -/
def compiledSimpleTokenBalanceOfPreservesState : Bool :=
  match compileFunctionNamed Compiler.Specs.simpleTokenSpec "balanceOf" with
  | .error _ => false
  | .ok block =>
      match block.params with
      | [addrParam] =>
          let initWorld : Verity.ContractState :=
            { Verity.defaultState with
              storageMap := fun i addr =>
                if i == 1 && addr == 42 then 500 else 0 }
          let init : TExecState :=
            { world := initWorld
              vars := { address := fun i =>
                          if i = addrParam.id then 42 else 0 } }
          match evalTBlock init block with
          | .ok _ => true
          | .revert _ => false
      | _ => false

/-- SimpleToken.balanceOf(addr=42): succeeds without reverting. -/
example : compiledSimpleTokenBalanceOfPreservesState = true := by native_decide

/-- End-to-end SimpleToken.totalSupply: compiled block preserves state (return is read-only). -/
def compiledSimpleTokenTotalSupplyPreservesState : Bool :=
  match compileFunctionNamed Compiler.Specs.simpleTokenSpec "totalSupply" with
  | .error _ => false
  | .ok block =>
      let initWorld : Verity.ContractState :=
        { Verity.defaultState with «storage» := fun i => if i = 2 then 1000 else 0 }
      let init : TExecState := { world := initWorld }
      match evalTBlock init block with
      | .ok _ => true
      | .revert _ => false

/-- SimpleToken.totalSupply: succeeds without reverting. -/
example : compiledSimpleTokenTotalSupplyPreservesState = true := by native_decide

/-- End-to-end SimpleToken.owner: compiled block preserves state (return is read-only). -/
def compiledSimpleTokenOwnerPreservesState : Bool :=
  match compileFunctionNamed Compiler.Specs.simpleTokenSpec "owner" with
  | .error _ => false
  | .ok block =>
      let initWorld : Verity.ContractState :=
        { Verity.defaultState with storageAddr := fun i => if i = 0 then 42 else 0 }
      let init : TExecState := { world := initWorld }
      match evalTBlock init block with
      | .ok _ => true
      | .revert _ => false

/-- SimpleToken.owner: succeeds without reverting. -/
example : compiledSimpleTokenOwnerPreservesState = true := by native_decide

open Compiler.CompilationModel in
/-- SimpleToken.totalSupply compilation correctness follows from the generic theorem. -/
example (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment simpleTokenFields),
      supportedStmtFragmentsToStmts fragments =
        [Stmt.return (Expr.storage "totalSupply")] ∧
      execCompiledSupportedStmtFragments simpleTokenFields init fragments =
        execSourceSupportedStmtFragments simpleTokenFields init fragments :=
  simpleToken_totalSupply_correctness init

open Compiler.CompilationModel in
/-- SimpleToken.owner compilation correctness follows from the generic theorem. -/
example (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment simpleTokenFields),
      supportedStmtFragmentsToStmts fragments =
        [Stmt.return (Expr.storage "owner")] ∧
      execCompiledSupportedStmtFragments simpleTokenFields init fragments =
        execSourceSupportedStmtFragments simpleTokenFields init fragments :=
  simpleToken_owner_correctness init

open Compiler.CompilationModel in
/-- Timestamp-write + stop pattern belongs to the supported fragment grammar. -/
example : SupportedStmtList simpleTokenFields
    [ Stmt.letVar "ts" Expr.blockTimestamp
    , Stmt.setStorage "totalSupply" (Expr.localVar "ts")
    , Stmt.stop ] :=
  witness_requireClausesThenLetBlockTimestampSetStorageLocalStop_supported

open Compiler.CompilationModel in
/-- Timestamp-write + stop correctness follows from the supported-list theorem. -/
example (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment simpleTokenFields),
      supportedStmtFragmentsToStmts fragments =
        [ Stmt.letVar "ts" Expr.blockTimestamp
        , Stmt.setStorage "totalSupply" (Expr.localVar "ts")
        , Stmt.stop ] ∧
      execCompiledSupportedStmtFragments simpleTokenFields init fragments =
        execSourceSupportedStmtFragments simpleTokenFields init fragments :=
  compile_supported_stmt_list_semantics simpleTokenFields init _
    witness_requireClausesThenLetBlockTimestampSetStorageLocalStop_supported

open Compiler.CompilationModel in
/-- Literal raw-log pattern belongs to the supported fragment grammar. -/
example : SupportedStmtList simpleTokenFields
    [Stmt.rawLog [Expr.literal 1, Expr.literal 2] (Expr.literal 0) (Expr.literal 64)] :=
  witness_requireClausesThenRawLogLiterals_supported

open Compiler.CompilationModel in
/-- Literal raw-log correctness follows from the supported-list theorem. -/
example (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment simpleTokenFields),
      supportedStmtFragmentsToStmts fragments =
        [Stmt.rawLog [Expr.literal 1, Expr.literal 2] (Expr.literal 0) (Expr.literal 64)] ∧
      execCompiledSupportedStmtFragments simpleTokenFields init fragments =
        execSourceSupportedStmtFragments simpleTokenFields init fragments :=
  compile_supported_stmt_list_semantics simpleTokenFields init _
    witness_requireClausesThenRawLogLiterals_supported

open Compiler.CompilationModel in
/-- Four-topic raw-log boundary pattern is admitted by the supported grammar. -/
example : SupportedStmtList simpleTokenFields
    [Stmt.rawLog [Expr.literal 1, Expr.literal 2, Expr.literal 3, Expr.literal 4]
      (Expr.literal 0) (Expr.literal 64)] := by
  refine ⟨[.requireClausesThenRawLogLiterals [] [1, 2, 3, 4] 0 64 (by decide)], rfl⟩

open Compiler.CompilationModel in
/-- Four-topic raw-log boundary correctness follows from the supported-list theorem. -/
example (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment simpleTokenFields),
      supportedStmtFragmentsToStmts fragments =
        [Stmt.rawLog [Expr.literal 1, Expr.literal 2, Expr.literal 3, Expr.literal 4]
          (Expr.literal 0) (Expr.literal 64)] ∧
      execCompiledSupportedStmtFragments simpleTokenFields init fragments =
        execSourceSupportedStmtFragments simpleTokenFields init fragments := by
  refine compile_supported_stmt_list_semantics simpleTokenFields init _ ?_
  refine ⟨[.requireClausesThenRawLogLiterals [] [1, 2, 3, 4] 0 64 (by decide)], rfl⟩

open Compiler.CompilationModel in
/-- Mapping return semantics preservation: compiled matches source for `return (mapping field caller)`. -/
example (fields : List Field)
    (fieldName : String) (slotIdx : Nat)
    (init : TExecState)
    (hSlot : findFieldSlot fields fieldName = some slotIdx) :
    execCompiledReturnMappingCaller fields fieldName init =
      execSourceReturnMappingCaller init slotIdx :=
  compile_return_mapping_caller_semantics fields fieldName slotIdx init hSlot

-- ============================================================================
-- ERC20 compilation tests
-- ============================================================================

/-- End-to-end ERC20.totalSupply: compiled block executes without reverting. -/
def compiledERC20TotalSupplyPreservesState : Bool :=
  match compileFunctionNamed Compiler.Specs.erc20Spec "totalSupply" with
  | .error _ => false
  | .ok block =>
      let initWorld : Verity.ContractState :=
        { Verity.defaultState with «storage» := fun i => if i = 1 then 42000 else 0 }
      let init : TExecState := { world := initWorld }
      match evalTBlock init block with
      | .ok _ => true
      | .revert _ => false

/-- ERC20.totalSupply: succeeds without reverting. -/
example : compiledERC20TotalSupplyPreservesState = true := by native_decide

/-- End-to-end ERC20.owner: compiled block executes without reverting. -/
def compiledERC20OwnerPreservesState : Bool :=
  match compileFunctionNamed Compiler.Specs.erc20Spec "owner" with
  | .error _ => false
  | .ok block =>
      let initWorld : Verity.ContractState :=
        { Verity.defaultState with storageAddr := fun i => if i = 0 then 0xDEAD else 0 }
      let init : TExecState := { world := initWorld }
      match evalTBlock init block with
      | .ok _ => true
      | .revert _ => false

/-- ERC20.owner: succeeds without reverting. -/
example : compiledERC20OwnerPreservesState = true := by native_decide

/-- End-to-end ERC20.balanceOf: compiled block executes without reverting. -/
def compiledERC20BalanceOfPreservesState : Bool :=
  match compileFunctionNamed Compiler.Specs.erc20Spec "balanceOf" with
  | .error _ => false
  | .ok block =>
      match block.params with
      | [addrParam] =>
          let initWorld : Verity.ContractState :=
            { Verity.defaultState with
              storageMap := fun i addr =>
                if i == 2 && addr == 42 then 500 else 0 }
          let init : TExecState :=
            { world := initWorld
              vars := { address := fun i =>
                          if i = addrParam.id then 42 else 0 } }
          match evalTBlock init block with
          | .ok _ => true
          | .revert _ => false
      | _ => false

/-- ERC20.balanceOf: succeeds without reverting. -/
example : compiledERC20BalanceOfPreservesState = true := by native_decide

/-- End-to-end ERC20.allowanceOf: compiled block executes without reverting. -/
def compiledERC20AllowanceOfPreservesState : Bool :=
  match compileFunctionNamed Compiler.Specs.erc20Spec "allowanceOf" with
  | .error _ => false
  | .ok block =>
      match block.params with
      | [ownerParam, spenderParam] =>
          let initWorld : Verity.ContractState :=
            { Verity.defaultState with
              storageMap2 := fun i a1 a2 =>
                if i == 3 && a1 == 100 && a2 == 200 then 750 else 0 }
          let init : TExecState :=
            { world := initWorld
              vars := { address := fun i =>
                          if i = ownerParam.id then 100
                          else if i = spenderParam.id then 200
                          else 0 } }
          match evalTBlock init block with
          | .ok _ => true
          | .revert _ => false
      | _ => false

/-- ERC20.allowanceOf: succeeds without reverting. -/
example : compiledERC20AllowanceOfPreservesState = true := by native_decide

/-- End-to-end ERC20.approve: compiled block executes without reverting. -/
def compiledERC20ApprovePreservesState : Bool :=
  match compileFunctionNamed Compiler.Specs.erc20Spec "approve" with
  | .error _ => false
  | .ok block =>
      match block.params with
      | [spenderParam, amountParam] =>
          let initWorld : Verity.ContractState :=
            { Verity.defaultState with storageMap2 := fun _ _ _ => 0 }
          let init : TExecState :=
            { world := initWorld
              env := { Verity.Env.ofWorld initWorld with sender := 0xCAFE }
              vars := { address := fun i =>
                          if i = spenderParam.id then 300 else 0
                        uint256 := fun i =>
                          if i = amountParam.id then 999 else 0 } }
          match evalTBlock init block with
          | .ok _ => true
          | .revert _ => false
      | _ => false

/-- ERC20.approve: succeeds without reverting. -/
example : compiledERC20ApprovePreservesState = true := by native_decide

open Compiler.CompilationModel in
/-- ERC20.totalSupply correctness instantiation. -/
example (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment erc20Fields),
      supportedStmtFragmentsToStmts fragments =
        [ Stmt.letVar "currentSupply" (Expr.storage "totalSupplySlot")
        , Stmt.return (Expr.localVar "currentSupply") ] ∧
      execCompiledSupportedStmtFragments erc20Fields init fragments =
        execSourceSupportedStmtFragments erc20Fields init fragments :=
  erc20_totalSupply_correctness init

open Compiler.CompilationModel in
/-- Admin `setOwner` pattern belongs to the supported fragment grammar. -/
example : SupportedStmtList adminPatternFields
    [ Stmt.letVar "sender" Expr.caller
    , Stmt.letVar "ownerVar" (Expr.storage "owner")
    , Stmt.require (Expr.eq (Expr.localVar "sender") (Expr.localVar "ownerVar")) "not owner"
    , Stmt.require (Expr.logicalNot (Expr.eq (Expr.param "newOwner") (Expr.localVar "ownerVar")))
        "already owner"
    , Stmt.setStorage "owner" (Expr.param "newOwner")
    , Stmt.stop ] :=
  witness_letCallerLetStorageAddrReqEqReqNeqSetStorageAddrParamStop_owner_supported

open Compiler.CompilationModel in
/-- Admin `setFeeRecipient` pattern belongs to the supported fragment grammar. -/
example : SupportedStmtList adminPatternFields
    [ Stmt.letVar "sender" Expr.caller
    , Stmt.letVar "currentFeeRecipient" (Expr.storage "feeRecipient")
    , Stmt.require (Expr.eq (Expr.localVar "sender") (Expr.localVar "currentFeeRecipient"))
        "not fee recipient"
    , Stmt.require
        (Expr.logicalNot (Expr.eq (Expr.param "newFeeRecipient") (Expr.localVar "currentFeeRecipient")))
        "already fee recipient"
    , Stmt.setStorage "feeRecipient" (Expr.param "newFeeRecipient")
    , Stmt.stop ] :=
  witness_letCallerLetStorageAddrReqEqReqNeqSetStorageAddrParamStop_feeRecipient_supported

open Compiler.CompilationModel in
/-- Owner-auth `setFeeRecipient` pattern belongs to the supported fragment grammar. -/
example : SupportedStmtList adminPatternFields
    [ Stmt.letVar "sender" Expr.caller
    , Stmt.letVar "ownerVar" (Expr.storage "owner")
    , Stmt.require (Expr.eq (Expr.localVar "sender") (Expr.localVar "ownerVar")) "not owner"
    , Stmt.letVar "currentFeeRecipient" (Expr.storage "feeRecipient")
    , Stmt.require
        (Expr.logicalNot (Expr.eq (Expr.param "newFeeRecipient") (Expr.localVar "currentFeeRecipient")))
        "already fee recipient"
    , Stmt.setStorage "feeRecipient" (Expr.param "newFeeRecipient")
    , Stmt.stop ] :=
  witness_letCallerLetStorageAddrReqEqLetStorageAddrReqNeqSetStorageAddrParamStop_feeRecipient_supported

open Compiler.CompilationModel in
/-- `setOwner` supported-list compilation correctness instantiation. -/
example (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment adminPatternFields),
      supportedStmtFragmentsToStmts fragments =
        [ Stmt.letVar "sender" Expr.caller
        , Stmt.letVar "ownerVar" (Expr.storage "owner")
        , Stmt.require (Expr.eq (Expr.localVar "sender") (Expr.localVar "ownerVar")) "not owner"
        , Stmt.require (Expr.logicalNot (Expr.eq (Expr.param "newOwner") (Expr.localVar "ownerVar")))
            "already owner"
        , Stmt.setStorage "owner" (Expr.param "newOwner")
        , Stmt.stop ] ∧
      execCompiledSupportedStmtFragments adminPatternFields init fragments =
        execSourceSupportedStmtFragments adminPatternFields init fragments :=
  compile_supported_stmt_list_semantics adminPatternFields init _
    witness_letCallerLetStorageAddrReqEqReqNeqSetStorageAddrParamStop_owner_supported

open Compiler.CompilationModel in
/-- `setFeeRecipient` supported-list compilation correctness instantiation. -/
example (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment adminPatternFields),
      supportedStmtFragmentsToStmts fragments =
        [ Stmt.letVar "sender" Expr.caller
        , Stmt.letVar "currentFeeRecipient" (Expr.storage "feeRecipient")
        , Stmt.require (Expr.eq (Expr.localVar "sender") (Expr.localVar "currentFeeRecipient"))
            "not fee recipient"
        , Stmt.require
            (Expr.logicalNot (Expr.eq (Expr.param "newFeeRecipient") (Expr.localVar "currentFeeRecipient")))
            "already fee recipient"
        , Stmt.setStorage "feeRecipient" (Expr.param "newFeeRecipient")
        , Stmt.stop ] ∧
      execCompiledSupportedStmtFragments adminPatternFields init fragments =
        execSourceSupportedStmtFragments adminPatternFields init fragments :=
  compile_supported_stmt_list_semantics adminPatternFields init _
    witness_letCallerLetStorageAddrReqEqReqNeqSetStorageAddrParamStop_feeRecipient_supported

open Compiler.CompilationModel in
/-- Owner-auth `setFeeRecipient` supported-list compilation correctness instantiation. -/
example (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment adminPatternFields),
      supportedStmtFragmentsToStmts fragments =
        [ Stmt.letVar "sender" Expr.caller
        , Stmt.letVar "ownerVar" (Expr.storage "owner")
        , Stmt.require (Expr.eq (Expr.localVar "sender") (Expr.localVar "ownerVar")) "not owner"
        , Stmt.letVar "currentFeeRecipient" (Expr.storage "feeRecipient")
        , Stmt.require
            (Expr.logicalNot (Expr.eq (Expr.param "newFeeRecipient") (Expr.localVar "currentFeeRecipient")))
            "already fee recipient"
        , Stmt.setStorage "feeRecipient" (Expr.param "newFeeRecipient")
        , Stmt.stop ] ∧
      execCompiledSupportedStmtFragments adminPatternFields init fragments =
        execSourceSupportedStmtFragments adminPatternFields init fragments :=
  compile_supported_stmt_list_semantics adminPatternFields init _
    witness_letCallerLetStorageAddrReqEqLetStorageAddrReqNeqSetStorageAddrParamStop_feeRecipient_supported

open Compiler.CompilationModel in
/-- ERC20.owner correctness instantiation. -/
example (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment erc20Fields),
      supportedStmtFragmentsToStmts fragments =
        [ Stmt.letVar "currentOwner" (Expr.storage "ownerSlot")
        , Stmt.return (Expr.localVar "currentOwner") ] ∧
      execCompiledSupportedStmtFragments erc20Fields init fragments =
        execSourceSupportedStmtFragments erc20Fields init fragments :=
  erc20_owner_correctness init

open Compiler.CompilationModel in
/-- ERC20.balanceOf correctness instantiation. -/
example (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment erc20Fields),
      supportedStmtFragmentsToStmts fragments =
        [ Stmt.letVar "currentBalance" (Expr.mapping "balancesSlot" (Expr.param "addr"))
        , Stmt.return (Expr.localVar "currentBalance") ] ∧
      execCompiledSupportedStmtFragments erc20Fields init fragments =
        execSourceSupportedStmtFragments erc20Fields init fragments :=
  erc20_balanceOf_correctness init

open Compiler.CompilationModel in
/-- ERC20.allowanceOf correctness instantiation. -/
example (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment erc20Fields),
      supportedStmtFragmentsToStmts fragments =
        [ Stmt.letVar "currentAllowance"
            (Expr.mapping2 "allowancesSlot" (Expr.param "ownerAddr") (Expr.param "spender"))
        , Stmt.return (Expr.localVar "currentAllowance") ] ∧
      execCompiledSupportedStmtFragments erc20Fields init fragments =
        execSourceSupportedStmtFragments erc20Fields init fragments :=
  erc20_allowanceOf_correctness init

open Compiler.CompilationModel in
/-- ERC20.approve correctness instantiation. -/
example (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment erc20Fields),
      supportedStmtFragmentsToStmts fragments =
        [ Stmt.letVar "sender" Expr.caller
        , Stmt.setMapping2 "allowancesSlot" (Expr.localVar "sender")
            (Expr.param "spender") (Expr.param "amount")
        , Stmt.stop ] ∧
      execCompiledSupportedStmtFragments erc20Fields init fragments =
        execSourceSupportedStmtFragments erc20Fields init fragments :=
  erc20_approve_correctness init

-- ============================================================
-- ERC721 bridge theorem tests
-- ============================================================

/-- End-to-end ERC721.getApproved: compiled block executes without reverting. -/
def compiledERC721GetApprovedPreservesState : Bool :=
  match compileFunctionNamed Compiler.Specs.erc721Spec "getApproved" with
  | .error _ => false
  | .ok block =>
      match block.params with
      | [tokenIdParam] =>
          let initWorld : Verity.ContractState :=
            { Verity.defaultState with
              storageMapUint := fun i key =>
                if i == 4 && key == 7 then 999 else 0 }
          let init : TExecState :=
            { world := initWorld
              vars := { uint256 := fun i =>
                          if i = tokenIdParam.id then 7 else 0 } }
          match evalTBlock init block with
          | .ok _ => true
          | .revert _ => false
      | _ => false

/-- ERC721.getApproved: succeeds without reverting. -/
example : compiledERC721GetApprovedPreservesState = true := by native_decide

/-- End-to-end ERC721.approve: compiled block executes without reverting. -/
def compiledERC721ApprovePreservesState : Bool :=
  match compileFunctionNamed Compiler.Specs.erc721Spec "approve" with
  | .error _ => false
  | .ok block =>
      match block.params with
      | [approvedParam, tokenIdParam] =>
          let initWorld : Verity.ContractState := Verity.defaultState
          let init : TExecState :=
            { world := initWorld
              vars := { uint256 := fun i =>
                          if i = approvedParam.id then 33
                          else if i = tokenIdParam.id then 7
                          else 0 } }
          match evalTBlock init block with
          | .ok _ => true
          | .revert _ => false
      | _ => false

/-- ERC721.approve: succeeds without reverting. -/
example : compiledERC721ApprovePreservesState = true := by native_decide

open Compiler.CompilationModel in
/-- ERC721.getApproved correctness instantiation. -/
example (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment erc721Fields),
      supportedStmtFragmentsToStmts fragments =
        [ Stmt.letVar "approvedWord" (Expr.mappingUint "tokenApprovalsSlot" (Expr.param "tokenId"))
        , Stmt.return (Expr.localVar "approvedWord") ] ∧
      execCompiledSupportedStmtFragments erc721Fields init fragments =
        execSourceSupportedStmtFragments erc721Fields init fragments :=
  erc721_getApproved_correctness init

open Compiler.CompilationModel in
/-- ERC721.approve correctness instantiation. -/
example (init : TExecState) :
    ∃ fragments : List (SupportedStmtFragment erc721Fields),
      supportedStmtFragmentsToStmts fragments =
        [ Stmt.setMappingUint "tokenApprovalsSlot" (Expr.param "tokenId") (Expr.param "approved")
        , Stmt.stop ] ∧
      execCompiledSupportedStmtFragments erc721Fields init fragments =
        execSourceSupportedStmtFragments erc721Fields init fragments :=
  erc721_approve_correctness init

end Verity.Core.Free
