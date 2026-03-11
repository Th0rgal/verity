/-
  IRInterpreter: Execution semantics for IR (Yul-based intermediate representation)

  This defines how IR contracts execute, enabling proofs that spec→IR compilation preserves semantics.

  Key differences from SpecInterpreter:
  - IR uses Yul expressions (ident, call) instead of high-level Spec expressions (storage, param)
  - IR has explicit variables and assignment instead of automatic scoping
  - IR is lower-level but simpler to reason about than full spec interpreter

  All functions in this module are **total** (no `partial` annotations):
  - Expression evaluators use structural recursion on expression size (exprSize/exprsSize)
  - Statement executors use an explicit fuel parameter
-/

import Compiler.IR
import Compiler.CompilationModel
import Compiler.Proofs.MappingSlot
import Compiler.Proofs.YulGeneration.Builtins
import Verity.Core

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.Yul
open Verity.Core
open Compiler.Proofs

/-! Size measures for termination proofs. -/
/-!
The helper-aware compiled semantics below is currently kept as executable
`partial def`s. That is sufficient for runtime tests and for pinning the future
theorem target, but the first conservative-extension proof tracked in `#1638`
will likely need a theorem-friendly total or inductive mirror of this surface.
-/
mutual
def exprSize : YulExpr → Nat
  | .call _ args => exprsSize args + 2
  | _ => 1

def exprsSize : List YulExpr → Nat
  | [] => 0
  | e :: es => exprSize e + exprsSize es + 1
end

/-! ## Execution State for IR -/

structure IRState where
  /-- Variable bindings (name → value) -/
  vars : List (String × Nat)
  /-- Storage slots (slot → value) -/
  storage : Nat → Nat
  /-- Memory words (offset → value) -/
  memory : Nat → Nat
  /-- Calldata words (argument index → value) -/
  calldata : List Nat
  /-- Return value (if any) -/
  returnValue : Option Nat
  /-- Sender address -/
  sender : Nat
  /-- Msg.value seen by `callvalue()`. -/
  msgValue : Nat := 0
  /-- Contract address seen by `address()`. -/
  thisAddress : Nat := 0
  /-- Block timestamp seen by `timestamp()`. -/
  blockTimestamp : Nat := 0
  /-- Block number seen by `number()`. -/
  blockNumber : Nat := 0
  /-- Chain id seen by `chainid()`. -/
  chainId : Nat := 0
  /-- Blob base fee seen by `blobbasefee()`. -/
  blobBaseFee : Nat := 0
  /-- Function selector (4-byte value used by calldataload(0)) -/
  selector : Nat
  /-- Emitted log records for this execution. -/
  events : List (List Nat) := []
  deriving Nonempty

/-- Initial state for IR execution -/
def IRState.initial (sender : Nat) : IRState :=
  { vars := []
    storage := fun _ => 0
    memory := fun _ => 0
    calldata := []
    returnValue := none
    sender := sender
    msgValue := 0
    thisAddress := 0
    blockTimestamp := 0
    blockNumber := 0
    chainId := 0
    blobBaseFee := 0
    selector := 0
    events := [] }

/-- Lookup variable in state -/
def IRState.getVar (s : IRState) (name : String) : Option Nat :=
  s.vars.find? (·.1 == name) |>.map (·.2)

/-- Set variable in state -/
def IRState.setVar (s : IRState) (name : String) (value : Nat) : IRState :=
  { s with vars := (name, value) :: s.vars.filter (·.1 != name) }

/-- Set several variables in order, matching the left-to-right binding behavior used
by parameter initialization and multi-return helper calls. -/
def IRState.setVars (s : IRState) (bindings : List (String × Nat)) : IRState :=
  bindings.foldl (fun st (name, value) => st.setVar name value) s

/-- Decoded internal helper definition from `IRContract.internalFunctions`. -/
structure IRInternalFunctionDef where
  name : String
  params : List String
  rets : List String
  body : List YulStmt

/-- View a stored internal-function statement as a decoded helper definition. -/
def irInternalFunctionDefOfStmt? : YulStmt → Option IRInternalFunctionDef
  | .funcDef name params rets body => some { name, params, rets, body }
  | _ => none

/-- Look up a helper function in the contract-local internal function table. -/
def findInternalFunction? (contract : IRContract) (name : String) :
    Option IRInternalFunctionDef :=
  (contract.internalFunctions.filterMap irInternalFunctionDefOfStmt?).find? (fun fn => fn.name = name)

/-- Helper-aware expression evaluation result, which can thread stateful helper-call
effects or propagate control-flow effects out of expression position. -/
inductive IRExprEvalResult
  | value (value : Nat) (state : IRState)
  | stop (state : IRState)
  | return (value : Nat) (state : IRState)
  | revert (state : IRState)
  deriving Nonempty

/-- Helper-aware call / argument-list evaluation result, carrying either a list of
values or an early control-flow effect. -/
inductive IRValuesEvalResult
  | values (values : List Nat) (state : IRState)
  | stop (state : IRState)
  | return (value : Nat) (state : IRState)
  | revert (state : IRState)
  deriving Nonempty

/-- Helper-aware statement execution result. `leave` is propagated explicitly so
internal Yul helper bodies can exit without aborting the whole external function. -/
inductive IRExecResultWithInternals
  | continue (state : IRState)
  | return (value : Nat) (state : IRState)
  | stop (state : IRState)
  | revert (state : IRState)
  | leave (state : IRState)
  deriving Nonempty

/-! ## IR Expression Evaluation (Total)

Expression evaluators use structural recursion on expression size, matching the
pattern already used by `evalYulExpr` in `Semantics.lean`. The `exprSize`/`exprsSize`
measures from Semantics.lean are reused.
-/

/-!
Runtime Yul mapping slots are derived via `keccak(baseSlot, key)`. IR proof
semantics call through `MappingSlot`; the active proof backend is `keccak`
(see `activeMappingSlotBackend`), so mapping addressing in `mappingSlot`/`sload`/
`sstore` follows Solidity's flat keccak-derived storage slots.
-/

mutual

/-- Evaluate a list of Yul expressions in the IR context.

Total: uses `exprsSize` for termination (structural recursion on expression tree). -/
def evalIRExprs (state : IRState) : List YulExpr → Option (List Nat)
  | [] => some []
  | e :: es => do
    let v ← evalIRExpr state e
    let vs ← evalIRExprs state es
    pure (v :: vs)
termination_by es => exprsSize es
decreasing_by
  all_goals
    simp [exprsSize]
    omega

/-- Evaluate an IR function call by evaluating all arguments first, then dispatching.

Total: uses `exprsSize args + 1` for termination. Evaluating args decreases the measure.

NOTE: This function always evaluates all arguments via `evalIRExprs` before dispatching,
matching the structure of `evalYulCall` in Semantics.lean. For `sload`, mapping slot
routing uses `Compiler.Proofs.abstractDecodeMappingSlot` on the evaluated slot value
(not pattern-matching on the argument expression). This makes the function structurally
identical to the Yul version, enabling direct equivalence proofs without axioms. -/
def evalIRCall (state : IRState) (func : String) : List YulExpr → Option Nat
  | args => do
    let argVals ← evalIRExprs state args
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext
      Compiler.Proofs.YulGeneration.defaultBuiltinBackend
      state.storage state.sender state.msgValue state.thisAddress state.blockTimestamp
      state.blockNumber state.chainId state.blobBaseFee state.selector state.calldata func argVals
termination_by args => exprsSize args + 1
decreasing_by
  omega

/-- Evaluate a Yul expression in the IR context.

Total: uses `exprSize` for termination (structural recursion on expression tree). -/
def evalIRExpr (state : IRState) : YulExpr → Option Nat
  | .lit n => some n
  | .hex n => some n
  | .str _ => none  -- Strings not supported in our IR subset
  | .ident name => state.getVar name
  | .call func args => evalIRCall state func args
termination_by e => exprSize e
decreasing_by
  simp [exprSize]

end -- mutual

private def restoreCallerVars (callerState calleeState : IRState) : IRState :=
  { calleeState with vars := callerState.vars }

private def internalReturnValues (state : IRState) (retNames : List String) : List Nat :=
  retNames.map (fun name => (state.getVar name).getD 0)

/-- Legacy IR-theorem compatibility subset for external bodies. This excludes the
helper-only Yul forms whose semantics differ from the current helper-free
interpreter target (`letMany`, `leave`, `switch`, and `for`) while still
allowing nested blocks / branches so the conservative-extension theorem can
talk about today's compiled external-body shape explicitly. -/
inductive LegacyCompatibleExternalStmtList : List YulStmt → Prop
  | nil :
      LegacyCompatibleExternalStmtList []
  | comment (msg : String) (rest : List YulStmt) :
      LegacyCompatibleExternalStmtList rest →
      LegacyCompatibleExternalStmtList (.comment msg :: rest)
  | let_ (name : String) (value : YulExpr) (rest : List YulStmt) :
      LegacyCompatibleExternalStmtList rest →
      LegacyCompatibleExternalStmtList (.let_ name value :: rest)
  | assign (name : String) (value : YulExpr) (rest : List YulStmt) :
      LegacyCompatibleExternalStmtList rest →
      LegacyCompatibleExternalStmtList (.assign name value :: rest)
  | expr (value : YulExpr) (rest : List YulStmt) :
      LegacyCompatibleExternalStmtList rest →
      LegacyCompatibleExternalStmtList (.expr value :: rest)
  | if_ (cond : YulExpr) (body rest : List YulStmt) :
      LegacyCompatibleExternalStmtList body →
      LegacyCompatibleExternalStmtList rest →
      LegacyCompatibleExternalStmtList (.if_ cond body :: rest)
  | block (body rest : List YulStmt) :
      LegacyCompatibleExternalStmtList body →
      LegacyCompatibleExternalStmtList rest →
      LegacyCompatibleExternalStmtList (.block body :: rest)
  | funcDef (name : String) (params rets : List String) (body rest : List YulStmt) :
      LegacyCompatibleExternalStmtList body →
      LegacyCompatibleExternalStmtList rest →
      LegacyCompatibleExternalStmtList (.funcDef name params rets body :: rest)

abbrev LegacyCompatibleExternalStmt (stmt : YulStmt) : Prop :=
  LegacyCompatibleExternalStmtList [stmt]

mutual

/-- Evaluate a list of Yul expressions in the helper-aware IR context, threading
stateful internal helper effects left-to-right. -/
partial def evalIRExprsWithInternals
    (contract : IRContract) (fuel : Nat) (state : IRState) (exprs : List YulExpr) :
    IRValuesEvalResult :=
  match exprs with
  | [] => .values [] state
  | e :: es =>
      match evalIRExprWithInternals contract fuel state e with
      | .value v state' =>
          match evalIRExprsWithInternals contract fuel state' es with
          | .values vs state'' => .values (v :: vs) state''
          | .stop state'' => .stop state''
          | .return value state'' => .return value state''
          | .revert state'' => .revert state''
      | .stop state' => .stop state'
      | .return value state' => .return value state'
      | .revert state' => .revert state'

/-- Execute a contract-local helper call, propagating control-flow effects and
restoring the caller's local variable frame on all non-revert exits. -/
partial def execIRInternalFunctionWithInternals
    (contract : IRContract) (fuel : Nat) (callerState : IRState)
    (helper : IRInternalFunctionDef) (args : List Nat) : IRValuesEvalResult :=
  match fuel with
  | 0 => .revert callerState
  | Nat.succ fuel' =>
      if helper.params.length = args.length then
        let paramBindings := helper.params.zip args
        let retBindings := helper.rets.map (fun name => (name, 0))
        let calleeState := callerState.setVars (paramBindings ++ retBindings)
        match execIRStmtsWithInternals contract fuel' calleeState helper.body with
        | .continue finalState =>
            .values (internalReturnValues finalState helper.rets)
              (restoreCallerVars callerState finalState)
        | .leave finalState =>
            .values (internalReturnValues finalState helper.rets)
              (restoreCallerVars callerState finalState)
        | .stop finalState =>
            .stop (restoreCallerVars callerState finalState)
        | .return value finalState =>
            .return value (restoreCallerVars callerState finalState)
        | .revert _ =>
            .revert callerState
      else
        .revert callerState

/-- Evaluate a Yul call in the helper-aware IR context. Builtins remain pure, while
internal helper calls execute through `IRContract.internalFunctions`. -/
partial def evalIRCallWithInternals
    (contract : IRContract) (fuel : Nat) (state : IRState) (func : String)
    (args : List YulExpr) : IRValuesEvalResult :=
  match evalIRExprsWithInternals contract fuel state args with
  | .values argVals state' =>
      match findInternalFunction? contract func with
      | some helper =>
          execIRInternalFunctionWithInternals contract fuel state' helper argVals
      | none =>
          match Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext
              Compiler.Proofs.YulGeneration.defaultBuiltinBackend
              state'.storage state'.sender state'.msgValue state'.thisAddress
              state'.blockTimestamp state'.blockNumber state'.chainId state'.blobBaseFee
              state'.selector state'.calldata func argVals with
          | some value => .values [value] state'
          | none => .revert state'
  | .stop state' => .stop state'
  | .return value state' => .return value state'
  | .revert state' => .revert state'

/-- Evaluate a single expression in the helper-aware IR context. -/
partial def evalIRExprWithInternals
    (contract : IRContract) (fuel : Nat) (state : IRState) (expr : YulExpr) :
    IRExprEvalResult :=
  match expr with
  | .lit n => .value n state
  | .hex n => .value n state
  | .str _ => .revert state
  | .ident name =>
      match state.getVar name with
      | some value => .value value state
      | none => .revert state
  | .call func args =>
      match evalIRCallWithInternals contract fuel state func args with
      | .values [value] state' => .value value state'
      | .values _ state' => .revert state'
      | .stop state' => .stop state'
      | .return value state' => .return value state'
      | .revert state' => .revert state'

/-- Execute a single Yul statement in the helper-aware IR context. -/
partial def execIRStmtWithInternals
    (contract : IRContract) (fuel : Nat) (state : IRState) (stmt : YulStmt) :
    IRExecResultWithInternals :=
  match stmt with
  | .funcDef _ _ _ _ => .continue state
  | _ =>
    match fuel with
    | 0 => .revert state
    | Nat.succ fuel =>
      match stmt with
      | .comment _ => .continue state
      | .let_ name value =>
          match evalIRExprWithInternals contract fuel state value with
          | .value v state' => .continue (state'.setVar name v)
          | .stop state' => .stop state'
          | .return value' state' => .return value' state'
          | .revert state' => .revert state'
      | .letMany names value =>
          match value with
          | .call func args =>
              match evalIRCallWithInternals contract fuel state func args with
              | .values values state' =>
                  if names.length = values.length then
                    .continue (state'.setVars (names.zip values))
                  else
                    .revert state'
              | .stop state' => .stop state'
              | .return value' state' => .return value' state'
              | .revert state' => .revert state'
          | _ => .revert state
      | .assign name value =>
          match evalIRExprWithInternals contract fuel state value with
          | .value v state' => .continue (state'.setVar name v)
          | .stop state' => .stop state'
          | .return value' state' => .return value' state'
          | .revert state' => .revert state'
      | .leave => .leave state
      | .expr e =>
          match e with
          | .call "sstore" [slotExpr, valExpr] =>
              match evalIRExprsWithInternals contract fuel state [slotExpr, valExpr] with
              | .values [slot, val] state' =>
                  let updated := Compiler.Proofs.abstractStoreStorageOrMapping state'.storage slot val
                  .continue { state' with storage := updated }
              | .values _ state' => .revert state'
              | .stop state' => .stop state'
              | .return value' state' => .return value' state'
              | .revert state' => .revert state'
          | .call "mstore" [offsetExpr, valExpr] =>
              match evalIRExprsWithInternals contract fuel state [offsetExpr, valExpr] with
              | .values [offset, val] state' =>
                  .continue {
                    state' with
                    memory := fun o => if o = offset then val else state'.memory o
                  }
              | .values _ state' => .revert state'
              | .stop state' => .stop state'
              | .return value' state' => .return value' state'
              | .revert state' => .revert state'
          | .call "stop" [] => .stop state
          | .call "revert" [offsetExpr, sizeExpr] =>
              match evalIRExprsWithInternals contract fuel state [offsetExpr, sizeExpr] with
              | .values [_, _] state' => .revert state'
              | .values _ state' => .revert state'
              | .stop state' => .stop state'
              | .return value' state' => .return value' state'
              | .revert state' => .revert state'
          | .call "return" [offsetExpr, sizeExpr] =>
              match evalIRExprsWithInternals contract fuel state [offsetExpr, sizeExpr] with
              | .values [offset, size] state' =>
                  if size = 32 then
                    .return (state'.memory offset) state'
                  else
                    .return 0 state'
              | .values _ state' => .revert state'
              | .stop state' => .stop state'
              | .return value' state' => .return value' state'
              | .revert state' => .revert state'
          | _ =>
              match evalIRExprWithInternals contract fuel state e with
              | .value _ state' => .continue state'
              | .stop state' => .stop state'
              | .return value' state' => .return value' state'
              | .revert state' => .revert state'
      | .if_ cond body =>
          match evalIRExprWithInternals contract fuel state cond with
          | .value condValue state' =>
              if condValue ≠ 0 then
                execIRStmtsWithInternals contract fuel state' body
              else
                .continue state'
          | .stop state' => .stop state'
          | .return value state' => .return value state'
          | .revert state' => .revert state'
      | .switch expr cases defaultCase =>
          match evalIRExprWithInternals contract fuel state expr with
          | .value switchValue state' =>
              match cases.find? (·.1 == switchValue) with
              | some (_, body) => execIRStmtsWithInternals contract fuel state' body
              | none =>
                  match defaultCase with
                  | some body => execIRStmtsWithInternals contract fuel state' body
                  | none => .continue state'
          | .stop state' => .stop state'
          | .return value state' => .return value state'
          | .revert state' => .revert state'
      | .for_ init cond post body =>
          match execIRStmtsWithInternals contract fuel state init with
          | .continue state' =>
              match evalIRExprWithInternals contract fuel state' cond with
              | .value condValue state'' =>
                  if condValue ≠ 0 then
                    match execIRStmtsWithInternals contract fuel state'' body with
                    | .continue state''' =>
                        match execIRStmtsWithInternals contract fuel state''' post with
                        | .continue state'''' =>
                            execIRStmtWithInternals contract fuel state'''' (.for_ [] cond post body)
                        | .return value state'''' => .return value state''''
                        | .stop state'''' => .stop state''''
                        | .revert state'''' => .revert state''''
                        | .leave state'''' => .leave state''''
                    | .return value state''' => .return value state'''
                    | .stop state''' => .stop state'''
                    | .revert state''' => .revert state'''
                    | .leave state''' => .leave state'''
                  else
                    .continue state''
              | .stop state'' => .stop state''
              | .return value state'' => .return value state''
              | .revert state'' => .revert state''
          | .return value state' => .return value state'
          | .stop state' => .stop state'
          | .revert state' => .revert state'
          | .leave state' => .leave state'
      | .block stmts =>
          execIRStmtsWithInternals contract fuel state stmts
      | .funcDef _ _ _ _ => .continue state

/-- Execute a list of statements in the helper-aware IR context. -/
partial def execIRStmtsWithInternals
    (contract : IRContract) (fuel : Nat) (state : IRState) (stmts : List YulStmt) :
    IRExecResultWithInternals :=
  match stmts with
  | [] => .continue state
  | stmt :: rest =>
      match fuel with
      | 0 => .revert state
      | Nat.succ fuel' =>
          match execIRStmtWithInternals contract fuel' state stmt with
          | .continue state' => execIRStmtsWithInternals contract fuel' state' rest
          | .return value state' => .return value state'
          | .stop state' => .stop state'
          | .revert state' => .revert state'
          | .leave state' => .leave state'

end

/-! ## IR Statement Execution (Fuel-Based, Total)

Statement executors use an explicit fuel parameter to ensure totality.
This eliminates the need for `partial def` and the corresponding
`execIRStmtsFuel_adequate` axiom. The fuel-based versions are now the
canonical definitions.
-/

/-- Result of executing IR statements -/
inductive IRExecResult
  | continue (state : IRState)
  | return (value : Nat) (state : IRState)
  | stop (state : IRState)
  | revert (state : IRState)
  deriving Nonempty

mutual

/-- Execute a single Yul statement with fuel bound.

Total: uses explicit fuel parameter for recursion control.
When fuel is 0, execution reverts (safe fallback). -/
def execIRStmt : Nat → IRState → YulStmt → IRExecResult
  | _, state, .funcDef _ _ _ _ => .continue state
  | 0, state, _ => .revert state  -- Out of fuel
  | Nat.succ fuel, state, stmt =>
      match stmt with
      | .comment _ => .continue state
      | .let_ name value =>
          match evalIRExpr state value with
          | some v => .continue (state.setVar name v)
          | none => .revert state
      | .letMany _ _ => .revert state
      | .assign name value =>
          match evalIRExpr state value with
          | some v => .continue (state.setVar name v)
          | none => .revert state
      | .leave => .continue state
      | .expr e =>
          match e with
          | .call "sstore" [slotExpr, valExpr] =>
              match slotExpr with
              | .call "mappingSlot" [baseExpr, keyExpr] =>
                  match evalIRExpr state baseExpr, evalIRExpr state keyExpr, evalIRExpr state valExpr with
                  | some baseSlot, some key, some val =>
                      let updated := Compiler.Proofs.abstractStoreMappingEntry
                        state.storage baseSlot key val
                      .continue {
                        state with
                        storage := updated
                      }
                  | _, _, _ => .revert state
              | _ =>
                  match evalIRExpr state slotExpr, evalIRExpr state valExpr with
                  | some slot, some val =>
                      let updated := Compiler.Proofs.abstractStoreStorageOrMapping
                        state.storage slot val
                      .continue {
                        state with
                        storage := updated
                      }
                  | _, _ => .revert state
          | .call "mstore" [offsetExpr, valExpr] =>
              match evalIRExpr state offsetExpr, evalIRExpr state valExpr with
              | some offset, some val =>
                .continue { state with memory := fun o => if o = offset then val else state.memory o }
              | _, _ => .revert state
          | .call "stop" [] => .stop state
          | .call "revert" [_, _] => .revert state
          | .call "return" [offsetExpr, sizeExpr] =>
              match evalIRExpr state offsetExpr, evalIRExpr state sizeExpr with
              | some offset, some size =>
                if size = 32 then
                  .return (state.memory offset) state
                else
                  .return 0 state
              | _, _ => .revert state
          | _ =>
              -- Keep expression-statement behavior aligned with Yul:
              -- evaluate the expression and revert on evaluation failure.
              match evalIRExpr state e with
              | some _ => .continue state
              | none => .revert state
      | .if_ cond body =>
          match evalIRExpr state cond with
          | some c => if c ≠ 0 then execIRStmts fuel state body else .continue state
          | none => .revert state
      | .switch expr cases defaultCase =>
          match evalIRExpr state expr with
          | some v =>
            match cases.find? (·.1 == v) with
            | some (_, body) => execIRStmts fuel state body
            | none =>
              match defaultCase with
              | some body => execIRStmts fuel state body
              | none => .continue state
          | none => .revert state
      | .for_ init cond post body =>
          -- Execute init, then loop: check cond, run body, run post, repeat
          match execIRStmts fuel state init with
          | .continue s' =>
              match evalIRExpr s' cond with
              | some v =>
                  if v ≠ 0 then
                    match execIRStmts fuel s' body with
                    | .continue s'' =>
                        match execIRStmts fuel s'' post with
                        | .continue s''' => execIRStmt fuel s''' (.for_ [] cond post body)
                        | other => other
                    | other => other
                  else .continue s'
              | none => .revert s'
          | other => other
      | .block stmts => execIRStmts fuel state stmts
      | .funcDef _ _ _ _ => .continue state

/-- Execute a sequence of IR statements with fuel bound.

Total: uses explicit fuel parameter for recursion control. -/
def execIRStmts (fuel : Nat) (state : IRState) : List YulStmt → IRExecResult
  | [] => .continue state
  | stmt :: rest =>
      match fuel with
      | 0 => .revert state
      | Nat.succ fuel =>
          match execIRStmt fuel state stmt with
          | .continue s' => execIRStmts fuel s' rest
          | .return v s => .return v s
          | .stop s => .stop s
          | .revert s => .revert s

end -- mutual

@[simp] theorem execIRStmt_stop_succ (fuel : Nat) (state : IRState) :
    execIRStmt (Nat.succ fuel) state (YulStmt.expr (YulExpr.call "stop" [])) =
      .stop state := by
  simp [execIRStmt]

@[simp] theorem execIRStmt_stop_one_add (fuel : Nat) (state : IRState) :
    execIRStmt (1 + fuel) state (YulStmt.expr (YulExpr.call "stop" [])) =
      .stop state := by
  simp [execIRStmt_stop_succ, Nat.add_comm]

@[simp] theorem execIRStmt_stop_one_add_add (a b : Nat) (state : IRState) :
    execIRStmt (1 + a + b) state (YulStmt.expr (YulExpr.call "stop" [])) =
      .stop state := by
  simp [execIRStmt_stop_one_add, Nat.add_assoc]

@[simp] theorem execIRStmt_sstore_lit_lit_succ
    (fuel : Nat) (state : IRState) (slot val : Nat) :
    execIRStmt (Nat.succ fuel) state
      (YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, YulExpr.lit val])) =
      .continue { state with
        storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage slot val } := by
  simp [execIRStmt, evalIRExpr]

theorem execIRStmt_sstore_lit_expr_succ_of_eval
    (fuel : Nat) (state : IRState) (slot : Nat) (valExpr : YulExpr) (val : Nat)
    (hval : evalIRExpr state valExpr = some val) :
    execIRStmt (Nat.succ fuel) state
      (YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, valExpr])) =
      .continue { state with
        storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage slot val } := by
  simp [execIRStmt, evalIRExpr, hval]

theorem execIRStmts_sstore_lit_expr_then_stop_succ_succ_succ_of_eval
    (fuel : Nat) (state : IRState) (slot : Nat) (valExpr : YulExpr) (val : Nat)
    (hval : evalIRExpr state valExpr = some val) :
    execIRStmts (Nat.succ (Nat.succ (Nat.succ fuel))) state
      [YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, valExpr]), YulStmt.expr (YulExpr.call "stop" [])] =
      .stop { state with
        storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage slot val } := by
  simp [execIRStmts, execIRStmt, evalIRExpr, hval]

@[simp] theorem execIRStmts_single_stop_succ_succ (fuel : Nat) (state : IRState) :
    execIRStmts (Nat.succ (Nat.succ fuel)) state [YulStmt.expr (YulExpr.call "stop" [])] =
      .stop state := by
  simp [execIRStmts, execIRStmt]

/-- A top-level `length + 1` fuel budget is not sufficient once a single list
is wrapped in a `block`: entering the block consumes one step and leaves only
`1` fuel for the nested body, which immediately reverts on its first
statement. This is the minimal counterexample showing that body-level proofs
cannot be extended to `Stmt.ite`-compiled blocks while still using `length + 1`
as the sole fuel metric. -/
theorem execIRStmts_single_block_stop_length_insufficient
    (state : IRState) :
    execIRStmts
      ([YulStmt.block [YulStmt.expr (YulExpr.call "stop" [])]].length + 1)
      state
      [YulStmt.block [YulStmt.expr (YulExpr.call "stop" [])]] =
        .revert state := by
  simp [execIRStmts, execIRStmt]

/-! ## IR Function Execution -/

structure IRTransaction where
  sender : Nat
  msgValue : Nat := 0
  thisAddress : Nat := 0
  blockTimestamp : Nat := 0
  blockNumber : Nat := 0
  chainId : Nat := 0
  blobBaseFee : Nat := 0
  functionSelector : Nat
  args : List Nat
  deriving Repr

structure IRResult where
  success : Bool
  returnValue : Option Nat
  finalStorage : Nat → Nat
  finalMappings : Nat → Nat → Nat
  events : List (List Nat)

/-- Execute an IR function with given arguments.
Uses `sizeOf fn.body + 1` fuel, which is sufficient for any terminating execution
of a non-looping function body. -/
noncomputable def execIRFunction (fn : IRFunction) (args : List Nat) (initialState : IRState) : IRResult :=
  -- Initialize parameters as variables
  let stateWithParams := fn.params.zip args |>.foldl
    (fun s (p, v) => s.setVar p.name v)
    initialState

  match execIRStmts (sizeOf fn.body + 1) stateWithParams fn.body with
  | .continue s =>
    { success := true
      returnValue := s.returnValue
      finalStorage := s.storage
      finalMappings := Compiler.Proofs.storageAsMappings s.storage
      events := s.events }
  | .return v s =>
    { success := true
      returnValue := some v
      finalStorage := s.storage
      finalMappings := Compiler.Proofs.storageAsMappings s.storage
      events := s.events }
  | .stop s =>
    { success := true
      returnValue := none
      finalStorage := s.storage
      finalMappings := Compiler.Proofs.storageAsMappings s.storage
      events := s.events }
  | .revert _ =>
    { success := false
      returnValue := none
      -- On revert, storage and mappings roll back to the initial state
      finalStorage := initialState.storage
      finalMappings := Compiler.Proofs.storageAsMappings initialState.storage
      events := initialState.events }

/-- Execute an IR function against a contract-aware helper table using an explicit
extra helper budget on top of the usual body fuel. This leaves the existing
`execIRFunction` theorem surface untouched while encoding the compiled-side helper
composition target tracked in issue `#1638`. -/
noncomputable def execIRFunctionWithInternals
    (contract : IRContract) (helperFuel : Nat)
    (fn : IRFunction) (args : List Nat) (initialState : IRState) : IRResult :=
  let stateWithParams := fn.params.zip args |>.foldl
    (fun s (p, v) => s.setVar p.name v)
    initialState
  match execIRStmtsWithInternals contract (sizeOf fn.body + helperFuel + 1) stateWithParams fn.body with
  | .continue s =>
      { success := true
        returnValue := s.returnValue
        finalStorage := s.storage
        finalMappings := Compiler.Proofs.storageAsMappings s.storage
        events := s.events }
  | .leave s =>
      { success := true
        returnValue := s.returnValue
        finalStorage := s.storage
        finalMappings := Compiler.Proofs.storageAsMappings s.storage
        events := s.events }
  | .return v s =>
      { success := true
        returnValue := some v
        finalStorage := s.storage
        finalMappings := Compiler.Proofs.storageAsMappings s.storage
        events := s.events }
  | .stop s =>
      { success := true
        returnValue := none
        finalStorage := s.storage
        finalMappings := Compiler.Proofs.storageAsMappings s.storage
        events := s.events }
  | .revert _ =>
      { success := false
        returnValue := none
        finalStorage := initialState.storage
        finalMappings := Compiler.Proofs.storageAsMappings initialState.storage
        events := initialState.events }

/-- Interpret an entire IR contract execution -/
noncomputable def interpretIR (contract : IRContract) (tx : IRTransaction) (initialState : IRState) : IRResult :=
  -- Execution sender and selector come from the transaction (matches SpecInterpreter)
  let initialState := {
    initialState with
    sender := tx.sender
    msgValue := tx.msgValue
    thisAddress := tx.thisAddress
    blockTimestamp := tx.blockTimestamp
    blockNumber := tx.blockNumber
    chainId := tx.chainId
    blobBaseFee := tx.blobBaseFee
    calldata := tx.args
    selector := tx.functionSelector
  }

  -- Find matching function by selector
  match contract.functions.find? (·.selector == tx.functionSelector) with
  | some fn =>
    if _ : fn.params.length ≤ tx.args.length then
      execIRFunction fn tx.args initialState
    else
      { success := false
        returnValue := none
        finalStorage := initialState.storage
        finalMappings := Compiler.Proofs.storageAsMappings initialState.storage
        events := initialState.events }
  | none =>
    { success := false
      returnValue := none
      finalStorage := initialState.storage
      finalMappings := Compiler.Proofs.storageAsMappings initialState.storage
      events := initialState.events }

/-- Contract-aware runtime interpretation with explicit helper fuel. This is the
compiled-side semantic target for future helper-summary composition proofs; the
existing `interpretIR` remains the current public theorem target on the helper-free
fragment. -/
noncomputable def interpretIRWithInternals
    (contract : IRContract) (helperFuel : Nat)
    (tx : IRTransaction) (initialState : IRState) : IRResult :=
  let initialState := {
    initialState with
    sender := tx.sender
    msgValue := tx.msgValue
    thisAddress := tx.thisAddress
    blockTimestamp := tx.blockTimestamp
    blockNumber := tx.blockNumber
    chainId := tx.chainId
    blobBaseFee := tx.blobBaseFee
    calldata := tx.args
    selector := tx.functionSelector
  }
  match contract.functions.find? (·.selector == tx.functionSelector) with
  | some fn =>
      if _ : fn.params.length ≤ tx.args.length then
        execIRFunctionWithInternals contract helperFuel fn tx.args initialState
      else
        { success := false
          returnValue := none
          finalStorage := initialState.storage
          finalMappings := Compiler.Proofs.storageAsMappings initialState.storage
          events := initialState.events }
  | none =>
      { success := false
        returnValue := none
        finalStorage := initialState.storage
        finalMappings := Compiler.Proofs.storageAsMappings initialState.storage
        events := initialState.events }

@[simp] theorem findInternalFunction?_eq_none_of_internalFunctions_nil
    (contract : IRContract) (name : String)
    (hinternal : contract.internalFunctions = []) :
    findInternalFunction? contract name = none := by
  simp [findInternalFunction?, hinternal]

private def shortCalldataRegressionContract : IRContract :=
  { name := "ShortCalldataRegression"
    deploy := []
    constructorPayable := false
    functions := [
      { name := "store"
        selector := 0x12345678
        params := [{ name := "value", ty := .uint256 }]
        ret := .unit
        payable := false
        body := [
          YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit 0, YulExpr.ident "value"]),
          YulStmt.expr (YulExpr.call "stop" [])
        ] }
    ]
    usesMapping := false }

example :
    (interpretIR shortCalldataRegressionContract
      { sender := 7, functionSelector := 0x12345678, args := [] }
      (IRState.initial 0)).success = false := by
  simp [interpretIR, shortCalldataRegressionContract, IRState.initial]

example :
    let result := interpretIR shortCalldataRegressionContract
      { sender := 7, functionSelector := 0x12345678, args := [99] }
      (IRState.initial 0)
    result.success = true ∧ result.finalStorage 0 = 99 := by
  simp [interpretIR, execIRFunction, execIRStmts, execIRStmt, evalIRExpr,
    shortCalldataRegressionContract, IRState.initial, IRState.setVar, IRState.getVar]

end Compiler.Proofs.IRGeneration
