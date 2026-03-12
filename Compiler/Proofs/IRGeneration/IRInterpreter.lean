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
mutual
def exprSize : YulExpr → Nat
  | .call _ args => exprsSize args + 2
  | _ => 1

def exprsSize : List YulExpr → Nat
  | [] => 0
  | e :: es => exprSize e + exprsSize es + 1
end

private theorem exprSize_lt_exprsSize_cons (e : YulExpr) (es : List YulExpr) :
    exprSize e < exprsSize (e :: es) := by
  simp [exprsSize]
  omega

private theorem exprsSize_tail_lt_exprsSize_cons (e : YulExpr) (es : List YulExpr) :
    exprsSize es < exprsSize (e :: es) := by
  simp [exprsSize]
  omega

private theorem exprsSize_lt_exprSize_call (func : String) (args : List YulExpr) :
    exprsSize args < exprSize (.call func args) := by
  simp [exprSize]

private theorem exprs_head_measure_decreases (fuel : Nat) (e : YulExpr) (es : List YulExpr) :
    Prod.Lex (fun x y => x < y) (fun x y => x < y)
      (fuel, exprSize e) (fuel, exprsSize (e :: es)) := by
  rw [Prod.lex_iff]
  exact Or.inr ⟨rfl, exprSize_lt_exprsSize_cons e es⟩

private theorem exprs_tail_measure_decreases (fuel : Nat) (e : YulExpr) (es : List YulExpr) :
    Prod.Lex (fun x y => x < y) (fun x y => x < y)
      (fuel, exprsSize es) (fuel, exprsSize (e :: es)) := by
  rw [Prod.lex_iff]
  exact Or.inr ⟨rfl, exprsSize_tail_lt_exprsSize_cons e es⟩

private theorem expr_call_measure_decreases (fuel : Nat) (func : String) (args : List YulExpr) :
    Prod.Lex (fun x y => x < y) (fun x y => x < y)
      (fuel, exprsSize args + 1) (fuel, exprSize (.call func args)) := by
  rw [Prod.lex_iff]
  simp [exprSize]

private theorem pairLex_same_fst_succ (a b : Nat) :
    Prod.Lex (fun x y => x < y) (fun x y => x < y) (a, b) (a, b + 1) := by
  rw [Prod.lex_iff]
  omega

private theorem internal_call_measure_decreases (fuel measure : Nat) :
    Prod.Lex (fun x y => x < y) (fun x y => x < y) (fuel, 0) (fuel.succ, measure + 1) := by
  rw [Prod.lex_iff]
  exact Or.inl (Nat.lt_succ_self fuel)

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

/-- Internal helper calls execute with a fresh local-variable frame. They keep the
caller's storage / memory / transaction context, but only helper params and
declared return slots are in scope at function entry. -/
private def prepareInternalCalleeState
    (callerState : IRState) (helper : IRInternalFunctionDef) (args : List Nat) : IRState :=
  let paramBindings := helper.params.zip args
  let retBindings := helper.rets.map (fun name => (name, 0))
  { callerState with vars := [] }.setVars (paramBindings ++ retBindings)

@[simp] private theorem prepareInternalCalleeState_vars
    (callerState : IRState) (helper : IRInternalFunctionDef) (args : List Nat) :
    (prepareInternalCalleeState callerState helper args).vars =
      ({ callerState with vars := [] }.setVars
        (helper.params.zip args ++ helper.rets.map (fun name => (name, 0)))).vars := by
  simp [prepareInternalCalleeState]

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

/-- Weaker compiled-side witness: only the externally callable function bodies
remain inside the current legacy-compatible Yul subset. This is the witness that
is plausibly derivable from supported external compile outputs even when the full
compiled contract still carries internal helper definitions. -/
def LegacyCompatibleExternalBodies (contract : IRContract) : Prop :=
  ∀ fn ∈ contract.functions, LegacyCompatibleExternalStmtList fn.body

mutual

/-- Evaluate a list of Yul expressions in the helper-aware IR context, threading
stateful internal helper effects left-to-right. -/
def evalIRExprsWithInternals
    (contract : IRContract) (fuel : Nat) (state : IRState) :
    List YulExpr → IRValuesEvalResult
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
termination_by exprs => (fuel, exprsSize exprs)
decreasing_by
  any_goals exact exprs_head_measure_decreases fuel e es
  any_goals exact exprs_tail_measure_decreases fuel e es

/-- Execute a contract-local helper call, propagating control-flow effects and
restoring the caller's local variable frame on all non-revert exits. -/
def execIRInternalFunctionWithInternals
    (contract : IRContract) :
    Nat → IRState → IRInternalFunctionDef → List Nat → IRValuesEvalResult
  | 0, callerState, _helper, _args => .revert callerState
  | Nat.succ fuel', callerState, helper, args =>
      if helper.params.length = args.length then
        let calleeState := prepareInternalCalleeState callerState helper args
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
termination_by fuel => (fuel, 0)
decreasing_by all_goals simp_wf; all_goals omega

/-- Evaluate a Yul call in the helper-aware IR context. Builtins remain pure, while
internal helper calls execute through `IRContract.internalFunctions`. -/
def evalIRCallWithInternals
    (contract : IRContract) (fuel : Nat) (state : IRState) (func : String) :
    List YulExpr → IRValuesEvalResult
  | args =>
    match evalIRExprsWithInternals contract fuel state args with
  | .values argVals state' =>
      match findInternalFunction? contract func with
      | some helper =>
          match fuel with
          | 0 => .revert state'
          | Nat.succ fuel' =>
              execIRInternalFunctionWithInternals contract fuel' state' helper argVals
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
termination_by args => (fuel, exprsSize args + 1)
decreasing_by
  any_goals exact pairLex_same_fst_succ fuel (exprsSize args)
  any_goals exact internal_call_measure_decreases fuel' _

 /-- Evaluate a single expression in the helper-aware IR context. -/
def evalIRExprWithInternals
    (contract : IRContract) (fuel : Nat) (state : IRState) :
    YulExpr → IRExprEvalResult
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
termination_by expr => (fuel, exprSize expr)
decreasing_by
  exact expr_call_measure_decreases fuel func args

/-- Execute a single Yul statement in the helper-aware IR context. -/
def execIRStmtWithInternals
    (contract : IRContract) :
    Nat → IRState → YulStmt → IRExecResultWithInternals
  | _, state, .funcDef _ _ _ _ => .continue state
  | 0, state, _ => .revert state
  | Nat.succ fuel, state, stmt =>
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
              match slotExpr with
              | .call "mappingSlot" [baseExpr, keyExpr] =>
                  match evalIRExprWithInternals contract fuel state baseExpr with
                  | .value baseSlot state' =>
                      match evalIRExprWithInternals contract fuel state' keyExpr with
                      | .value key state'' =>
                          match evalIRExprWithInternals contract fuel state'' valExpr with
                          | .value val state''' =>
                              let updated := Compiler.Proofs.abstractStoreMappingEntry
                                state'''.storage baseSlot key val
                              .continue { state''' with storage := updated }
                          | .stop state''' => .stop state'''
                          | .return value' state''' => .return value' state'''
                          | .revert state''' => .revert state'''
                      | .stop state'' => .stop state''
                      | .return value' state'' => .return value' state''
                      | .revert state'' => .revert state''
                  | .stop state' => .stop state'
                  | .return value' state' => .return value' state'
                  | .revert state' => .revert state'
              | _ =>
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
termination_by fuel => (fuel, 0)
decreasing_by all_goals simp_wf; all_goals omega

/-- Execute a list of statements in the helper-aware IR context. -/
def execIRStmtsWithInternals
    (contract : IRContract) (fuel : Nat) (state : IRState) :
    List YulStmt → IRExecResultWithInternals
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
termination_by stmts => (fuel, stmts.length)
decreasing_by all_goals simp_wf; all_goals omega

end

/-! ## Helper Scope Sanity Checks -/

/-- Helper bodies do not inherit caller-only locals. If a helper reads an
identifier that is neither a parameter nor a declared return slot, execution
fails against the fresh callee frame instead of silently seeing the caller's
binding. -/
theorem execIRInternalFunctionWithInternals_hides_caller_only_locals :
    let callerState := (IRState.initial 0).setVar "callerOnly" 7
    let helper : IRInternalFunctionDef :=
      { name := "helper"
        params := []
        rets := ["ret"]
        body := [.assign "ret" (.ident "callerOnly")] }
    let contract : IRContract :=
      { name := "C"
        deploy := []
        functions := []
        usesMapping := false }
    execIRInternalFunctionWithInternals contract 2 callerState helper [] =
      .revert callerState := by
  simp [execIRInternalFunctionWithInternals, prepareInternalCalleeState,
    execIRStmtsWithInternals, execIRStmtWithInternals,
    IRState.initial, IRState.setVar, IRState.setVars]

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

/-- The first compiled-side helper retarget theorem only needs the current
helper-free runtime-contract shape: no internal helpers and legacy-compatible
external bodies. Encoding that shape as a proposition keeps the remaining
conservative-extension step machine-checkable instead of prose-only. -/
def LegacyCompatibleRuntimeContract (contract : IRContract) : Prop :=
  contract.internalFunctions = [] ∧
    LegacyCompatibleExternalBodies contract

theorem legacyCompatibleExternalBodies_of_legacyCompatibleRuntimeContract
    (contract : IRContract) :
    LegacyCompatibleRuntimeContract contract →
      LegacyCompatibleExternalBodies contract := by
  intro hlegacy
  exact hlegacy.2

/-- Exact first conservative-extension theorem target for the helper-aware IR
interpreter: on helper-free runtime contracts with legacy-compatible external
bodies, zero-helper-fuel helper-aware interpretation should coincide with the
current public `interpretIR` target. This is intentionally stronger than the
eventual whole-contract retarget domain for full compile outputs: compiled
contracts may still carry `internalFunctions` even when their external runtime
bodies remain inside `LegacyCompatibleExternalBodies`. -/
def InterpretIRWithInternalsZeroConservativeExtensionGoal
    (contract : IRContract) : Prop :=
  LegacyCompatibleRuntimeContract contract →
    ∀ tx initialState,
      interpretIRWithInternals contract 0 tx initialState =
        interpretIR contract tx initialState

/-- Compositional proof surface for the first compiled-side helper retarget theorem.
Rather than treating `InterpretIRWithInternalsZeroConservativeExtensionGoal` as a
single opaque proof obligation, this packages the expected compatibility lemmas
that should be proved first and then composed into the top-level contract theorem. -/
structure InterpretIRWithInternalsZeroConservativeExtensionInterfaces
    (contract : IRContract) : Prop where
  exprCompatibility :
    contract.internalFunctions = [] →
      ∀ fuel state expr,
        evalIRExprWithInternals contract fuel state expr =
          match evalIRExpr state expr with
          | some value => .value value state
          | none => .revert state
  exprListCompatibility :
    contract.internalFunctions = [] →
      ∀ fuel state exprs,
        evalIRExprsWithInternals contract fuel state exprs =
          match evalIRExprs state exprs with
          | some values => .values values state
          | none => .revert state
  stmtCompatibility :
    contract.internalFunctions = [] →
      ∀ fuel state stmt,
        LegacyCompatibleExternalStmt stmt →
          execIRStmtWithInternals contract fuel state stmt =
            match execIRStmt fuel state stmt with
            | .continue next => .continue next
            | .return value next => .return value next
            | .stop next => .stop next
            | .revert next => .revert next
  stmtListCompatibility :
    contract.internalFunctions = [] →
      ∀ fuel state stmts,
        LegacyCompatibleExternalStmtList stmts →
          execIRStmtsWithInternals contract fuel state stmts =
            match execIRStmts fuel state stmts with
            | .continue next => .continue next
            | .return value next => .return value next
            | .stop next => .stop next
            | .revert next => .revert next
  functionCompatibility :
    contract.internalFunctions = [] →
      ∀ fn args initialState,
        LegacyCompatibleExternalStmtList fn.body →
          execIRFunctionWithInternals contract 0 fn args initialState =
            execIRFunction fn args initialState

mutual

theorem evalIRExprWithInternals_eq_evalIRExpr_of_no_internal
    (contract : IRContract)
    (hinternal : contract.internalFunctions = []) :
    ∀ fuel state expr,
      evalIRExprWithInternals contract fuel state expr =
        match evalIRExpr state expr with
        | some value => .value value state
        | none => .revert state
  | fuel, state, .lit n => by
      simp [evalIRExprWithInternals, evalIRExpr]
  | fuel, state, .hex n => by
      simp [evalIRExprWithInternals, evalIRExpr]
  | fuel, state, .str s => by
      simp [evalIRExprWithInternals, evalIRExpr]
  | fuel, state, .ident name => by
      cases hget : state.getVar name <;>
        simp [evalIRExprWithInternals, evalIRExpr, hget]
  | fuel, state, .call func args => by
      rw [evalIRExprWithInternals, evalIRExpr, evalIRCall, evalIRCallWithInternals,
        evalIRExprsWithInternals_eq_evalIRExprs_of_no_internal contract hinternal fuel state args]
      cases hargs : evalIRExprs state args with
      | none =>
          simp
      | some argVals =>
          cases hbuiltin :
              Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext
                Compiler.Proofs.YulGeneration.defaultBuiltinBackend
                state.storage state.sender state.msgValue state.thisAddress state.blockTimestamp
                state.blockNumber state.chainId state.blobBaseFee state.selector state.calldata func argVals with
          | none =>
              simp [findInternalFunction?_eq_none_of_internalFunctions_nil, hinternal, hbuiltin]
          | some value =>
              simp [findInternalFunction?_eq_none_of_internalFunctions_nil, hinternal, hbuiltin]

theorem evalIRExprsWithInternals_eq_evalIRExprs_of_no_internal
    (contract : IRContract)
    (hinternal : contract.internalFunctions = []) :
    ∀ fuel state exprs,
      evalIRExprsWithInternals contract fuel state exprs =
        match evalIRExprs state exprs with
        | some values => .values values state
        | none => .revert state
  | fuel, state, [] => by
      simp [evalIRExprsWithInternals, evalIRExprs]
  | fuel, state, expr :: exprs => by
      rw [evalIRExprsWithInternals,
        evalIRExprWithInternals_eq_evalIRExpr_of_no_internal contract hinternal fuel state expr]
      cases hexpr : evalIRExpr state expr <;>
        cases htail : evalIRExprs state exprs <;>
          simp [evalIRExprs, hexpr, htail,
            evalIRExprsWithInternals_eq_evalIRExprs_of_no_internal contract hinternal fuel state exprs]

end

/-- Per-expression disjointness: no nested function call in this expression
resolves to an internal function in the given contract's runtime table.
This is strictly weaker than `contract.internalFunctions = []`: a contract
MAY carry internal helper definitions as long as no expression inside an
external function body actually calls one of them. The compiler ensures
this by emitting `internal_`-prefixed names only through `Stmt.internalCall`
and `Stmt.internalCallAssign`, never inside legacy external-body expressions. -/
def yulExprCallsDisjointFromInternalTable (contract : IRContract) : YulExpr → Prop
  | .lit _ | .hex _ | .str _ | .ident _ => True
  | .call func args =>
      findInternalFunction? contract func = none ∧
      ∀ arg, arg ∈ args → yulExprCallsDisjointFromInternalTable contract arg

def yulExprsCallsDisjointFromInternalTable (contract : IRContract) :
    List YulExpr → Prop
  | [] => True
  | e :: es =>
      yulExprCallsDisjointFromInternalTable contract e ∧
      yulExprsCallsDisjointFromInternalTable contract es

/-- Extract the `findInternalFunction? ... = none` part of a call-level
disjointness hypothesis. -/
theorem yulExprCallsDisjointFromInternalTable_call_func
    {contract : IRContract} {func : String} {args : List YulExpr}
    (h : yulExprCallsDisjointFromInternalTable contract (.call func args)) :
    findInternalFunction? contract func = none := by
  unfold yulExprCallsDisjointFromInternalTable at h; exact h.1

/-- Extract the per-argument disjointness from a call-level hypothesis. -/
theorem yulExprCallsDisjointFromInternalTable_call_args
    {contract : IRContract} {func : String} {args : List YulExpr}
    (h : yulExprCallsDisjointFromInternalTable contract (.call func args)) :
    ∀ arg, arg ∈ args → yulExprCallsDisjointFromInternalTable contract arg := by
  unfold yulExprCallsDisjointFromInternalTable at h; exact h.2

mutual
private theorem yulExprCallsDisjointFromInternalTable_of_nil_aux
    (contract : IRContract) (hinternal : contract.internalFunctions = [])
    (expr : YulExpr) :
    yulExprCallsDisjointFromInternalTable contract expr := by
  cases expr with
  | lit | hex | str | ident =>
      simp [yulExprCallsDisjointFromInternalTable]
  | call func args =>
      unfold yulExprCallsDisjointFromInternalTable
      exact ⟨findInternalFunction?_eq_none_of_internalFunctions_nil contract func hinternal,
        fun arg hmem => yulExprCallsDisjointFromInternalTable_of_nil_aux_list
          contract hinternal args arg hmem⟩

private theorem yulExprCallsDisjointFromInternalTable_of_nil_aux_list
    (contract : IRContract) (hinternal : contract.internalFunctions = [])
    (exprs : List YulExpr) (e : YulExpr) (hmem : e ∈ exprs) :
    yulExprCallsDisjointFromInternalTable contract e := by
  match exprs, hmem with
  | _ :: _, .head .. =>
      exact yulExprCallsDisjointFromInternalTable_of_nil_aux contract hinternal e
  | _ :: tl, .tail _ hmem' =>
      exact yulExprCallsDisjointFromInternalTable_of_nil_aux_list contract hinternal tl e hmem'
end

theorem yulExprCallsDisjointFromInternalTable_of_internalFunctions_nil
    (contract : IRContract) (hinternal : contract.internalFunctions = [])
    (expr : YulExpr) :
    yulExprCallsDisjointFromInternalTable contract expr :=
  yulExprCallsDisjointFromInternalTable_of_nil_aux contract hinternal expr

theorem yulExprsCallsDisjointFromInternalTable_of_internalFunctions_nil
    (contract : IRContract) (hinternal : contract.internalFunctions = [])
    (exprs : List YulExpr) :
    yulExprsCallsDisjointFromInternalTable contract exprs := by
  induction exprs with
  | nil => trivial
  | cons e es ih =>
      exact ⟨yulExprCallsDisjointFromInternalTable_of_internalFunctions_nil contract hinternal e, ih⟩

mutual

/-- Expression-level conservative extension under per-expression disjointness.
This is the generalization of `evalIRExprWithInternals_eq_evalIRExpr_of_no_internal`
that does not require `contract.internalFunctions = []`: it suffices that the
specific expression being evaluated does not reference any internal function in
the contract's runtime table. -/
theorem evalIRExprWithInternals_eq_evalIRExpr_of_callsDisjoint
    (contract : IRContract) :
    ∀ fuel state expr,
      yulExprCallsDisjointFromInternalTable contract expr →
      evalIRExprWithInternals contract fuel state expr =
        match evalIRExpr state expr with
        | some value => .value value state
        | none => .revert state
  | fuel, state, .lit n, _ => by
      simp [evalIRExprWithInternals, evalIRExpr]
  | fuel, state, .hex n, _ => by
      simp [evalIRExprWithInternals, evalIRExpr]
  | fuel, state, .str s, _ => by
      simp [evalIRExprWithInternals, evalIRExpr]
  | fuel, state, .ident name, _ => by
      cases hget : state.getVar name <;>
        simp [evalIRExprWithInternals, evalIRExpr, hget]
  | fuel, state, .call func args, hdisjoint => by
      have hfunc := yulExprCallsDisjointFromInternalTable_call_func hdisjoint
      have hargs_disjoint := yulExprCallsDisjointFromInternalTable_call_args hdisjoint
      rw [evalIRExprWithInternals, evalIRExpr, evalIRCall, evalIRCallWithInternals,
        evalIRExprsWithInternals_eq_evalIRExprs_of_callsDisjoint contract fuel state args
          hargs_disjoint]
      cases hargs : evalIRExprs state args with
      | none =>
          simp
      | some argVals =>
          cases hbuiltin :
              Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext
                Compiler.Proofs.YulGeneration.defaultBuiltinBackend
                state.storage state.sender state.msgValue state.thisAddress state.blockTimestamp
                state.blockNumber state.chainId state.blobBaseFee state.selector state.calldata func argVals with
          | none =>
              simp [hfunc, hbuiltin]
          | some value =>
              simp [hfunc, hbuiltin]

/-- Expression-list conservative extension under per-expression disjointness.
Generalizes `evalIRExprsWithInternals_eq_evalIRExprs_of_no_internal`. -/
theorem evalIRExprsWithInternals_eq_evalIRExprs_of_callsDisjoint
    (contract : IRContract) :
    ∀ fuel state exprs,
      (∀ e, e ∈ exprs → yulExprCallsDisjointFromInternalTable contract e) →
      evalIRExprsWithInternals contract fuel state exprs =
        match evalIRExprs state exprs with
        | some values => .values values state
        | none => .revert state
  | fuel, state, [], _ => by
      simp [evalIRExprsWithInternals, evalIRExprs]
  | fuel, state, expr :: exprs, hdisjoint => by
      have hexpr_disjoint : yulExprCallsDisjointFromInternalTable contract expr :=
        hdisjoint expr (List.mem_cons_self ..)
      have hrest_disjoint : ∀ e, e ∈ exprs →
          yulExprCallsDisjointFromInternalTable contract e :=
        fun e hmem => hdisjoint e (List.mem_cons_of_mem _ hmem)
      rw [evalIRExprsWithInternals,
        evalIRExprWithInternals_eq_evalIRExpr_of_callsDisjoint contract fuel state expr
          hexpr_disjoint]
      cases hexpr : evalIRExpr state expr <;>
        cases htail : evalIRExprs state exprs <;>
          simp [evalIRExprs, hexpr, htail,
            evalIRExprsWithInternals_eq_evalIRExprs_of_callsDisjoint contract fuel state exprs
              hrest_disjoint]

end

/-- Per-statement disjointness predicate (inductive): every nested expression in
the statement list is disjoint from the contract's internal function table.
Encoding as an inductive avoids the nested-inductive termination issue that
mutual `def` would cause on `YulStmt` / `List YulStmt`. -/
inductive YulStmtListCallsDisjointFromInternalTable
    (contract : IRContract) : List YulStmt → Prop
  | nil :
      YulStmtListCallsDisjointFromInternalTable contract []
  | comment (msg : String) (rest : List YulStmt) :
      YulStmtListCallsDisjointFromInternalTable contract rest →
      YulStmtListCallsDisjointFromInternalTable contract (.comment msg :: rest)
  | let_ (name : String) (value : YulExpr) (rest : List YulStmt) :
      yulExprCallsDisjointFromInternalTable contract value →
      YulStmtListCallsDisjointFromInternalTable contract rest →
      YulStmtListCallsDisjointFromInternalTable contract (.let_ name value :: rest)
  | assign (name : String) (value : YulExpr) (rest : List YulStmt) :
      yulExprCallsDisjointFromInternalTable contract value →
      YulStmtListCallsDisjointFromInternalTable contract rest →
      YulStmtListCallsDisjointFromInternalTable contract (.assign name value :: rest)
  | expr (value : YulExpr) (rest : List YulStmt) :
      yulExprCallsDisjointFromInternalTable contract value →
      YulStmtListCallsDisjointFromInternalTable contract rest →
      YulStmtListCallsDisjointFromInternalTable contract (.expr value :: rest)
  | if_ (cond : YulExpr) (body rest : List YulStmt) :
      yulExprCallsDisjointFromInternalTable contract cond →
      YulStmtListCallsDisjointFromInternalTable contract body →
      YulStmtListCallsDisjointFromInternalTable contract rest →
      YulStmtListCallsDisjointFromInternalTable contract (.if_ cond body :: rest)
  | block (body rest : List YulStmt) :
      YulStmtListCallsDisjointFromInternalTable contract body →
      YulStmtListCallsDisjointFromInternalTable contract rest →
      YulStmtListCallsDisjointFromInternalTable contract (.block body :: rest)
  | funcDef (name : String) (params rets : List String) (body rest : List YulStmt) :
      YulStmtListCallsDisjointFromInternalTable contract body →
      YulStmtListCallsDisjointFromInternalTable contract rest →
      YulStmtListCallsDisjointFromInternalTable contract (.funcDef name params rets body :: rest)
  | switch_ (expr : YulExpr)
      (cases : List (Nat × List YulStmt))
      (defaultCase : Option (List YulStmt))
      (rest : List YulStmt) :
      yulExprCallsDisjointFromInternalTable contract expr →
      (∀ c ∈ cases, YulStmtListCallsDisjointFromInternalTable contract c.2) →
      (∀ body, defaultCase = some body →
        YulStmtListCallsDisjointFromInternalTable contract body) →
      YulStmtListCallsDisjointFromInternalTable contract rest →
      YulStmtListCallsDisjointFromInternalTable contract
        (.switch expr cases defaultCase :: rest)
  | for_ (init : List YulStmt) (cond : YulExpr)
      (post body rest : List YulStmt) :
      YulStmtListCallsDisjointFromInternalTable contract init →
      yulExprCallsDisjointFromInternalTable contract cond →
      YulStmtListCallsDisjointFromInternalTable contract post →
      YulStmtListCallsDisjointFromInternalTable contract body →
      YulStmtListCallsDisjointFromInternalTable contract rest →
      YulStmtListCallsDisjointFromInternalTable contract
        (.for_ init cond post body :: rest)

/-- Single-statement wrapper: the singleton list is disjoint. -/
abbrev YulStmtCallsDisjointFromInternalTable
    (contract : IRContract) (stmt : YulStmt) : Prop :=
  YulStmtListCallsDisjointFromInternalTable contract [stmt]

/-- Generalized expr-stmt conservative extension under per-expression disjointness.
This does not require `contract.internalFunctions = []`: it suffices that the
specific expression is disjoint from the contract's internal function table.
The proof follows the same structure as `execIRStmtWithInternals_eq_execIRStmt_expr_of_no_internal`
but uses the `_of_callsDisjoint` expression theorems in place of the
`_of_no_internal` variants. -/
theorem execIRStmtWithInternals_eq_execIRStmt_expr_of_callsDisjoint
    (contract : IRContract) :
    ∀ fuel state expr,
      yulExprCallsDisjointFromInternalTable contract expr →
      execIRStmtWithInternals contract fuel state (.expr expr) =
        match execIRStmt fuel state (.expr expr) with
        | .continue next => .continue next
        | .return value next => .return value next
        | .stop next => .stop next
        | .revert next => .revert next
  | fuel, state, expr, hdisjoint => by
    cases fuel with
    | zero =>
        simp [execIRStmtWithInternals, execIRStmt]
    | succ fuel =>
        -- The proof parallels `_of_no_internal` (which uses `hinternal` everywhere);
        -- we thread `hdisjoint` to the expression-level `_of_callsDisjoint` instead.
        cases expr with
        | lit n =>
            cases hlit : evalIRExpr state (.lit n) <;>
              simp [execIRStmtWithInternals, execIRStmt,
                evalIRExprWithInternals_eq_evalIRExpr_of_callsDisjoint contract fuel state
                  (.lit n) hdisjoint,
                hlit]
        | hex n =>
            cases hhex : evalIRExpr state (.hex n) <;>
              simp [execIRStmtWithInternals, execIRStmt,
                evalIRExprWithInternals_eq_evalIRExpr_of_callsDisjoint contract fuel state
                  (.hex n) hdisjoint,
                hhex]
        | str s =>
            cases hstr : evalIRExpr state (.str s) <;>
              simp [execIRStmtWithInternals, execIRStmt,
                evalIRExprWithInternals_eq_evalIRExpr_of_callsDisjoint contract fuel state
                  (.str s) hdisjoint,
                hstr]
        | ident name =>
            cases hident : state.getVar name <;>
              simp [execIRStmtWithInternals, execIRStmt, evalIRExpr,
                evalIRExprWithInternals_eq_evalIRExpr_of_callsDisjoint contract fuel state
                  (.ident name) hdisjoint,
                hident]
        | call func args =>
            have hargs_d := yulExprCallsDisjointFromInternalTable_call_args hdisjoint
            -- Helper: list-level disjointness for the full args list
            have hexprs_args_d : ∀ e, e ∈ args →
                yulExprCallsDisjointFromInternalTable contract e := hargs_d
            cases args with
            | nil =>
                by_cases hstop : func = "stop"
                · subst hstop
                  simp [execIRStmtWithInternals, execIRStmt]
                · cases hcall : evalIRExpr state (.call func []) <;>
                    simp [execIRStmtWithInternals, execIRStmt,
                      evalIRExprWithInternals_eq_evalIRExpr_of_callsDisjoint contract fuel state
                        (.call func []) hdisjoint,
                      hstop, hcall]
            | cons arg rest =>
                cases rest with
                | nil =>
                    cases hcall : evalIRExpr state (.call func [arg]) <;>
                      simp [execIRStmtWithInternals, execIRStmt,
                        evalIRExprWithInternals_eq_evalIRExpr_of_callsDisjoint contract fuel state
                          (.call func [arg]) hdisjoint,
                        hcall]
                | cons arg2 rest =>
                    cases rest with
                    | nil =>
                        have harg_d : yulExprCallsDisjointFromInternalTable contract arg :=
                          hargs_d arg (List.mem_cons_self ..)
                        have harg2_d : yulExprCallsDisjointFromInternalTable contract arg2 :=
                          hargs_d arg2 (List.mem_cons_of_mem _ (List.mem_cons_self ..))
                        -- Two-element list disjointness for evalIRExprs rewriting
                        have hpair_d : ∀ e, e ∈ [arg, arg2] →
                            yulExprCallsDisjointFromInternalTable contract e := by
                          intro e hmem
                          simp [List.mem_cons] at hmem
                          rcases hmem with rfl | rfl <;> assumption
                        by_cases hsstore : func = "sstore"
                        · subst hsstore
                          -- sstore has special mappingSlot handling
                          cases arg with
                          | call sfunc sargs =>
                              by_cases hmap : sfunc = "mappingSlot"
                              · subst hmap
                                cases sargs with
                                | nil =>
                                    -- mappingSlot with 0 args — falls through to Exprs path
                                    cases hslot : evalIRExpr state (.call "mappingSlot" []) <;>
                                      cases hval : evalIRExpr state arg2 <;>
                                        simp [execIRStmtWithInternals, execIRStmt, evalIRExprs,
                                          evalIRExprsWithInternals_eq_evalIRExprs_of_callsDisjoint
                                            contract fuel state [.call "mappingSlot" [], arg2] hpair_d,
                                          hslot, hval]
                                | cons b1 srest =>
                                    cases srest with
                                    | nil =>
                                        -- mappingSlot with 1 arg — falls through
                                        cases hslot : evalIRExpr state (.call "mappingSlot" [b1]) <;>
                                          cases hval : evalIRExpr state arg2 <;>
                                            simp [execIRStmtWithInternals, execIRStmt, evalIRExprs,
                                              evalIRExprsWithInternals_eq_evalIRExprs_of_callsDisjoint
                                                contract fuel state [.call "mappingSlot" [b1], arg2] hpair_d,
                                              hslot, hval]
                                    | cons b2 srest2 =>
                                        cases srest2 with
                                        | nil =>
                                            -- mappingSlot with exactly 2 args — the special case
                                            have hbase_d : yulExprCallsDisjointFromInternalTable contract b1 := by
                                              exact yulExprCallsDisjointFromInternalTable_call_args harg_d
                                                b1 (List.mem_cons_self ..)
                                            have hkey_d : yulExprCallsDisjointFromInternalTable contract b2 := by
                                              exact yulExprCallsDisjointFromInternalTable_call_args harg_d
                                                b2 (List.mem_cons_of_mem _ (List.mem_cons_self ..))
                                            rw [execIRStmtWithInternals, execIRStmt]
                                            rw [evalIRExprWithInternals_eq_evalIRExpr_of_callsDisjoint
                                              contract fuel state b1 hbase_d]
                                            cases hbase : evalIRExpr state b1 with
                                            | none => simp
                                            | some baseSlot =>
                                                simp only []
                                                rw [evalIRExprWithInternals_eq_evalIRExpr_of_callsDisjoint
                                                  contract fuel state b2 hkey_d]
                                                cases hkey : evalIRExpr state b2 with
                                                | none => simp
                                                | some key =>
                                                    simp only []
                                                    rw [evalIRExprWithInternals_eq_evalIRExpr_of_callsDisjoint
                                                      contract fuel state arg2 harg2_d]
                                                    cases hval : evalIRExpr state arg2 <;> simp
                                        | cons b3 srest3 =>
                                            -- mappingSlot with 3+ args — falls through to Exprs path
                                            cases hslot : evalIRExpr state (.call "mappingSlot" (b1 :: b2 :: b3 :: srest3)) <;>
                                              cases hval : evalIRExpr state arg2 <;>
                                                simp [execIRStmtWithInternals, execIRStmt, evalIRExprs,
                                                  evalIRExprsWithInternals_eq_evalIRExprs_of_callsDisjoint
                                                    contract fuel state
                                                    [.call "mappingSlot" (b1 :: b2 :: b3 :: srest3), arg2] hpair_d,
                                                  hslot, hval]
                              · -- Non-mappingSlot call as slot expr — uses Exprs path
                                cases hslot : evalIRExpr state (.call sfunc sargs) <;>
                                  cases hval : evalIRExpr state arg2 <;>
                                    simp [execIRStmtWithInternals, execIRStmt, evalIRExprs, hmap,
                                      evalIRExprsWithInternals_eq_evalIRExprs_of_callsDisjoint
                                        contract fuel state [.call sfunc sargs, arg2] hpair_d,
                                      hslot, hval]
                          | lit n =>
                              cases hslot : evalIRExpr state (.lit n) <;>
                                cases hval : evalIRExpr state arg2 <;>
                                  simp [execIRStmtWithInternals, execIRStmt, evalIRExprs,
                                    evalIRExprsWithInternals_eq_evalIRExprs_of_callsDisjoint
                                      contract fuel state [.lit n, arg2] hpair_d,
                                    hslot, hval]
                          | hex n =>
                              cases hslot : evalIRExpr state (.hex n) <;>
                                cases hval : evalIRExpr state arg2 <;>
                                  simp [execIRStmtWithInternals, execIRStmt, evalIRExprs,
                                    evalIRExprsWithInternals_eq_evalIRExprs_of_callsDisjoint
                                      contract fuel state [.hex n, arg2] hpair_d,
                                    hslot, hval]
                          | str s =>
                              cases hslot : evalIRExpr state (.str s) <;>
                                cases hval : evalIRExpr state arg2 <;>
                                  simp [execIRStmtWithInternals, execIRStmt, evalIRExprs,
                                    evalIRExprsWithInternals_eq_evalIRExprs_of_callsDisjoint
                                      contract fuel state [.str s, arg2] hpair_d,
                                    hslot, hval]
                          | ident name =>
                              cases hslot : evalIRExpr state (.ident name) <;>
                                cases hval : evalIRExpr state arg2 <;>
                                  simp [execIRStmtWithInternals, execIRStmt, evalIRExprs,
                                    evalIRExprsWithInternals_eq_evalIRExprs_of_callsDisjoint
                                      contract fuel state [.ident name, arg2] hpair_d,
                                    hslot, hval]
                        · by_cases hmstore : func = "mstore"
                          · subst hmstore
                            -- mstore uses evalIRExprsWithInternals
                            cases hoffset : evalIRExpr state arg <;>
                              cases hval : evalIRExpr state arg2 <;>
                                simp [execIRStmtWithInternals, execIRStmt, evalIRExprs,
                                  evalIRExprsWithInternals_eq_evalIRExprs_of_callsDisjoint
                                    contract fuel state [arg, arg2] hpair_d,
                                  hoffset, hval]
                          · by_cases hrevert : func = "revert"
                            · subst hrevert
                              -- revert uses evalIRExprsWithInternals
                              cases hoffset : evalIRExpr state arg <;>
                                cases hsize : evalIRExpr state arg2 <;>
                                  simp [execIRStmtWithInternals, execIRStmt, evalIRExprs,
                                    evalIRExprsWithInternals_eq_evalIRExprs_of_callsDisjoint
                                      contract fuel state [arg, arg2] hpair_d,
                                    hoffset, hsize]
                            · by_cases hreturn : func = "return"
                              · subst hreturn
                                -- return uses evalIRExprsWithInternals + size = 32 branch
                                cases hoffset : evalIRExpr state arg with
                                | none =>
                                    cases hsize : evalIRExpr state arg2 <;>
                                      simp [execIRStmtWithInternals, execIRStmt, evalIRExprs,
                                        evalIRExprsWithInternals_eq_evalIRExprs_of_callsDisjoint
                                          contract fuel state [arg, arg2] hpair_d,
                                        hoffset, hsize]
                                | some offset =>
                                    cases hsize : evalIRExpr state arg2 with
                                    | none =>
                                        simp [execIRStmtWithInternals, execIRStmt, evalIRExprs,
                                          evalIRExprsWithInternals_eq_evalIRExprs_of_callsDisjoint
                                            contract fuel state [arg, arg2] hpair_d,
                                          hoffset, hsize]
                                    | some size =>
                                        by_cases h32 : size = 32 <;>
                                          simp [execIRStmtWithInternals, execIRStmt, evalIRExprs,
                                            evalIRExprsWithInternals_eq_evalIRExprs_of_callsDisjoint
                                              contract fuel state [arg, arg2] hpair_d,
                                            hoffset, hsize, h32]
                              · -- Generic two-arg call (not sstore/mstore/revert/return)
                                cases hcall : evalIRExpr state (.call func [arg, arg2]) <;>
                                  simp [execIRStmtWithInternals, execIRStmt,
                                    evalIRExprWithInternals_eq_evalIRExpr_of_callsDisjoint contract fuel state
                                      (.call func [arg, arg2]) hdisjoint,
                                    hsstore, hmstore, hrevert, hreturn, hcall]
                    | cons arg3 rest =>
                        cases hcall : evalIRExpr state (.call func (arg :: arg2 :: arg3 :: rest)) <;>
                          simp [execIRStmtWithInternals, execIRStmt,
                            evalIRExprWithInternals_eq_evalIRExpr_of_callsDisjoint contract fuel state
                              (.call func (arg :: arg2 :: arg3 :: rest)) hdisjoint,
                            hcall]

/-- Statement-list conservative extension under per-statement disjointness.
This is the generalization of `execIRStmtsWithInternals_eq_execIRStmts_of_exprCompatibility`
that does not require `contract.internalFunctions = []`: it suffices that every
statement in the list satisfies `YulStmtListCallsDisjointFromInternalTable`. -/
theorem execIRStmtsWithInternals_eq_execIRStmts_of_callsDisjoint
    (contract : IRContract) :
    ∀ fuel state stmts,
      YulStmtListCallsDisjointFromInternalTable contract stmts →
      execIRStmtsWithInternals contract fuel state stmts =
        match execIRStmts fuel state stmts with
        | .continue next => .continue next
        | .return value next => .return value next
        | .stop next => .stop next
        | .revert next => .revert next
  | fuel, state, stmts, hdisjoint => by
    induction hdisjoint generalizing fuel state with
    | nil =>
        cases fuel <;> simp [execIRStmtsWithInternals, execIRStmts]
    | comment msg rest hrest ih =>
        cases fuel with
        | zero =>
            simp [execIRStmtsWithInternals, execIRStmts]
        | succ fuel =>
            have hhead :
                execIRStmtWithInternals contract fuel state (.comment msg) =
                  match execIRStmt fuel state (.comment msg) with
                  | .continue next => .continue next
                  | .return value next => .return value next
                  | .stop next => .stop next
                  | .revert next => .revert next := by
              cases fuel <;> simp [execIRStmtWithInternals, execIRStmt]
            rw [execIRStmtsWithInternals, execIRStmts, hhead]
            cases hstep : execIRStmt fuel state (.comment msg) <;>
              simp [ih]
    | let_ name value rest hval_d hrest ih =>
        cases fuel with
        | zero =>
            simp [execIRStmtsWithInternals, execIRStmts]
        | succ fuel =>
            have hhead :
                execIRStmtWithInternals contract fuel state (.let_ name value) =
                  match execIRStmt fuel state (.let_ name value) with
                  | .continue next => .continue next
                  | .return value next => .return value next
                  | .stop next => .stop next
                  | .revert next => .revert next := by
              cases fuel with
              | zero =>
                  simp [execIRStmtWithInternals, execIRStmt]
              | succ fuel =>
                  cases hval : evalIRExpr state value <;>
                    simp [execIRStmtWithInternals, execIRStmt,
                      evalIRExprWithInternals_eq_evalIRExpr_of_callsDisjoint contract fuel state
                        value hval_d, hval]
            rw [execIRStmtsWithInternals, execIRStmts, hhead]
            cases hstep : execIRStmt fuel state (.let_ name value) <;>
              simp [ih]
    | assign name value rest hval_d hrest ih =>
        cases fuel with
        | zero =>
            simp [execIRStmtsWithInternals, execIRStmts]
        | succ fuel =>
            have hhead :
                execIRStmtWithInternals contract fuel state (.assign name value) =
                  match execIRStmt fuel state (.assign name value) with
                  | .continue next => .continue next
                  | .return value next => .return value next
                  | .stop next => .stop next
                  | .revert next => .revert next := by
              cases fuel with
              | zero =>
                  simp [execIRStmtWithInternals, execIRStmt]
              | succ fuel =>
                  cases hval : evalIRExpr state value <;>
                    simp [execIRStmtWithInternals, execIRStmt,
                      evalIRExprWithInternals_eq_evalIRExpr_of_callsDisjoint contract fuel state
                        value hval_d, hval]
            rw [execIRStmtsWithInternals, execIRStmts, hhead]
            cases hstep : execIRStmt fuel state (.assign name value) <;>
              simp [ih]
    | expr value rest hval_d hrest ih =>
        cases fuel with
        | zero =>
            simp [execIRStmtsWithInternals, execIRStmts]
        | succ fuel =>
            have hhead := execIRStmtWithInternals_eq_execIRStmt_expr_of_callsDisjoint
              contract fuel state value hval_d
            rw [execIRStmtsWithInternals, execIRStmts, hhead]
            cases hstep : execIRStmt fuel state (.expr value) <;>
              simp [ih]
    | if_ cond body rest hcond_d hbody hrest ihBody ihRest =>
        cases fuel with
        | zero =>
            simp [execIRStmtsWithInternals, execIRStmts]
        | succ fuel =>
            have hhead :
                execIRStmtWithInternals contract fuel state (.if_ cond body) =
                  match execIRStmt fuel state (.if_ cond body) with
                  | .continue next => .continue next
                  | .return value next => .return value next
                  | .stop next => .stop next
                  | .revert next => .revert next := by
              cases fuel with
              | zero =>
                  simp [execIRStmtWithInternals, execIRStmt]
              | succ fuel =>
                  rw [execIRStmtWithInternals, execIRStmt]
                  rw [evalIRExprWithInternals_eq_evalIRExpr_of_callsDisjoint contract fuel state
                    cond hcond_d]
                  cases hcond : evalIRExpr state cond with
                  | none =>
                      simp
                  | some condValue =>
                      by_cases hnonzero : condValue ≠ 0
                      · simp [hnonzero, ihBody fuel state]
                      · simp [hnonzero]
            rw [execIRStmtsWithInternals, execIRStmts, hhead]
            cases hstep : execIRStmt fuel state (.if_ cond body) <;>
              simp [ihRest]
    | block body rest hbody hrest ihBody ihRest =>
        cases fuel with
        | zero =>
            simp [execIRStmtsWithInternals, execIRStmts]
        | succ fuel =>
            have hhead :
                execIRStmtWithInternals contract fuel state (.block body) =
                  match execIRStmt fuel state (.block body) with
                  | .continue next => .continue next
                  | .return value next => .return value next
                  | .stop next => .stop next
                  | .revert next => .revert next := by
              cases fuel with
              | zero =>
                  simp [execIRStmtWithInternals, execIRStmt]
              | succ fuel =>
                  simpa [execIRStmtWithInternals, execIRStmt] using ihBody fuel state
            rw [execIRStmtsWithInternals, execIRStmts, hhead]
            cases hstep : execIRStmt fuel state (.block body) <;>
              simp [ihRest]
    | funcDef name params rets body rest hbody hrest ihBody ihRest =>
        cases fuel with
        | zero =>
            simp [execIRStmtsWithInternals, execIRStmts]
        | succ fuel =>
            have hhead :
                execIRStmtWithInternals contract fuel state (.funcDef name params rets body) =
                  match execIRStmt fuel state (.funcDef name params rets body) with
                  | .continue next => .continue next
                  | .return value next => .return value next
                  | .stop next => .stop next
                  | .revert next => .revert next := by
              simp [execIRStmtWithInternals, execIRStmt]
            rw [execIRStmtsWithInternals, execIRStmts, hhead]
            cases hstep : execIRStmt fuel state (.funcDef name params rets body) <;>
              simp [ihRest]
    | switch_ expr cases defaultCase rest hexpr_d hcases_d hdefault_d hrest
        ihCases ihDefault ihRest =>
        cases fuel with
        | zero =>
            simp [execIRStmtsWithInternals, execIRStmts]
        | succ fuel =>
            have hhead :
                execIRStmtWithInternals contract fuel state (.switch expr cases defaultCase) =
                  match execIRStmt fuel state (.switch expr cases defaultCase) with
                  | .continue next => .continue next
                  | .return value next => .return value next
                  | .stop next => .stop next
                  | .revert next => .revert next := by
              cases fuel with
              | zero =>
                  simp [execIRStmtWithInternals, execIRStmt]
              | succ fuel =>
                  simp only [execIRStmtWithInternals, execIRStmt]
                  rw [evalIRExprWithInternals_eq_evalIRExpr_of_callsDisjoint contract fuel state
                    expr hexpr_d]
                  cases hval : evalIRExpr state expr with
                  | none =>
                      simp
                  | some switchValue =>
                      cases hfind : cases.find? (·.1 == switchValue) with
                      | some match_ =>
                          obtain ⟨matchVal, matchBody⟩ := match_
                          simp only [hfind]
                          have hmem : (matchVal, matchBody) ∈ cases :=
                            List.mem_of_find?_eq_some hfind
                          exact ihCases (matchVal, matchBody) hmem fuel state
                      | none =>
                          simp only [hfind]
                          cases hdef : defaultCase with
                          | none =>
                              simp
                          | some defBody =>
                              exact ihDefault defBody hdef fuel state
            rw [execIRStmtsWithInternals, execIRStmts, hhead]
            cases hstep : execIRStmt fuel state (.switch expr cases defaultCase) <;>
              simp [ihRest]
    | for_ init cond post body rest hinit_d hcond_d hpost_d hbody_d hrest
        ihInit ihPost ihBody ihRest =>
        cases fuel with
        | zero =>
            simp [execIRStmtsWithInternals, execIRStmts]
        | succ fuel =>
            -- The for_ single-statement equivalence needs inner induction on fuel
            -- because the loop recurses: execIRStmtWithInternals ... (.for_ [] cond post body).
            -- Under disjointness, init/body/post all satisfy the stmt-list conservative
            -- extension, and the recursive call uses [] for init (trivially disjoint).
            have hhead :
                execIRStmtWithInternals contract fuel state (.for_ init cond post body) =
                  match execIRStmt fuel state (.for_ init cond post body) with
                  | .continue next => .continue next
                  | .return value next => .return value next
                  | .stop next => .stop next
                  | .revert next => .revert next := by
              -- We prove this by strong induction on fuel, using the stmt-list IHs.
              -- First, prove the general for_ equivalence for arbitrary init under
              -- the assumption that init/cond/post/body are all disjoint.
              suffices hgen : ∀ (f : Nat) (s : IRState) (initStmts : List YulStmt),
                  (∀ f' s', execIRStmtsWithInternals contract f' s' initStmts =
                    match execIRStmts f' s' initStmts with
                    | .continue n => .continue n | .return v n => .return v n
                    | .stop n => .stop n | .revert n => .revert n) →
                  execIRStmtWithInternals contract f s (.for_ initStmts cond post body) =
                    match execIRStmt f s (.for_ initStmts cond post body) with
                    | .continue next => .continue next
                    | .return value next => .return value next
                    | .stop next => .stop next
                    | .revert next => .revert next by
                exact hgen fuel state init (ihInit · ·)
              intro f
              induction f with
              | zero =>
                  intro s initStmts _
                  simp [execIRStmtWithInternals, execIRStmt]
              | succ f ihFuel =>
                  intro s initStmts hInitEq
                  simp only [execIRStmtWithInternals, execIRStmt]
                  -- Rewrite init execution
                  rw [hInitEq]
                  cases hInitStep : execIRStmts f s initStmts with
                  | «continue» s' =>
                      simp only []
                      -- Rewrite cond evaluation
                      rw [evalIRExprWithInternals_eq_evalIRExpr_of_callsDisjoint
                        contract f s' cond hcond_d]
                      cases hCondVal : evalIRExpr s' cond with
                      | none =>
                          simp
                      | some condValue =>
                          by_cases hnonzero : condValue ≠ 0
                          · simp only [if_pos hnonzero]
                            -- Rewrite body execution
                            rw [ihBody f s']
                            cases hBodyStep : execIRStmts f s' body with
                            | «continue» s'' =>
                                simp only []
                                -- Rewrite post execution
                                rw [ihPost f s'']
                                cases hPostStep : execIRStmts f s'' post with
                                | «continue» s''' =>
                                    simp only []
                                    -- Recursive call with [] init
                                    have hNilEq : ∀ f' s',
                                        execIRStmtsWithInternals contract f' s' [] =
                                          match execIRStmts f' s' [] with
                                          | .continue n => .continue n
                                          | .return v n => .return v n
                                          | .stop n => .stop n
                                          | .revert n => .revert n := by
                                      intro f' s'
                                      simp [execIRStmtsWithInternals, execIRStmts]
                                    exact ihFuel s''' [] hNilEq
                                | «return» v s''' => simp
                                | stop s''' => simp
                                | revert s''' => simp
                            | «return» v s'' => simp
                            | stop s'' => simp
                            | revert s'' => simp
                          · simp only [if_neg hnonzero]
                  | «return» v s' => simp
                  | stop s' => simp
                  | revert s' => simp
            rw [execIRStmtsWithInternals, execIRStmts, hhead]
            cases hstep : execIRStmt fuel state (.for_ init cond post body) <;>
              simp [ihRest]

/-- Backward-compatible bridge: `YulStmtListCallsDisjointFromInternalTable` holds
whenever `contract.internalFunctions = []` and the stmt list is legacy-compatible.
This ensures the new generalized theorem subsumes the existing `_of_no_internal`
and `_of_exprCompatibility` results. -/
theorem YulStmtListCallsDisjointFromInternalTable_of_internalFunctions_nil
    (contract : IRContract) (hinternal : contract.internalFunctions = [])
    (stmts : List YulStmt) (hlegacy : LegacyCompatibleExternalStmtList stmts) :
    YulStmtListCallsDisjointFromInternalTable contract stmts := by
  induction hlegacy with
  | nil =>
      exact .nil
  | comment msg rest _ ih =>
      exact .comment msg rest ih
  | let_ name value rest _ ih =>
      exact .let_ name value rest
        (yulExprCallsDisjointFromInternalTable_of_internalFunctions_nil contract hinternal value) ih
  | assign name value rest _ ih =>
      exact .assign name value rest
        (yulExprCallsDisjointFromInternalTable_of_internalFunctions_nil contract hinternal value) ih
  | expr value rest _ ih =>
      exact .expr value rest
        (yulExprCallsDisjointFromInternalTable_of_internalFunctions_nil contract hinternal value) ih
  | if_ cond body rest hbody _ ihBody ihRest =>
      exact .if_ cond body rest
        (yulExprCallsDisjointFromInternalTable_of_internalFunctions_nil contract hinternal cond) ihBody ihRest
  | block body rest hbody _ ihBody ihRest =>
      exact .block body rest ihBody ihRest
  | funcDef name params rets body rest hbody _ ihBody ihRest =>
      exact .funcDef name params rets body rest ihBody ihRest

/-- Helper-free helper-aware execution now preserves the legacy `mappingSlot`
`sstore` special case instead of routing it through the generic builtin path.
This removes a real semantic mismatch that would otherwise make the remaining
stmt-compatibility theorem false on mapping-backed contracts. -/
theorem execIRStmtWithInternals_sstore_mappingSlot_succ_of_no_internal
    (contract : IRContract)
    (hinternal : contract.internalFunctions = [])
    (fuel : Nat) (state : IRState)
    (baseExpr keyExpr valExpr : YulExpr)
    (baseSlot key val : Nat)
    (hbase : evalIRExpr state baseExpr = some baseSlot)
    (hkey : evalIRExpr state keyExpr = some key)
    (hval : evalIRExpr state valExpr = some val) :
    execIRStmtWithInternals contract (Nat.succ fuel) state
      (YulStmt.expr
        (YulExpr.call "sstore"
          [YulExpr.call "mappingSlot" [baseExpr, keyExpr], valExpr])) =
      .continue { state with
        storage := Compiler.Proofs.abstractStoreMappingEntry state.storage baseSlot key val } := by
  simp [execIRStmtWithInternals,
    evalIRExprWithInternals_eq_evalIRExpr_of_no_internal contract hinternal,
    hbase, hkey, hval]

/-- Expression statements that do not fall through the ordinary
`evalIRExprWithInternals` / `evalIRExpr` path and therefore need dedicated
compatibility lemmas on the helper-free compiled-side retarget track. -/
def exprStmtUsesDedicatedBuiltinSemantics : YulExpr → Bool
  | .call "sstore" [_, _] => true
  | .call "mstore" [_, _] => true
  | .call "stop" [] => true
  | .call "revert" [_, _] => true
  | .call "return" [_, _] => true
  | _ => false

/-- Helper-free helper-aware execution also preserves legacy `mstore` semantics.
This isolates `mstore` as a closed compiled-side subcase rather than leaving it
implicit inside the larger stmt-compatibility theorem. -/
theorem execIRStmtWithInternals_eq_execIRStmt_mstore_of_no_internal
    (contract : IRContract)
    (hinternal : contract.internalFunctions = [])
    (fuel : Nat) (state : IRState)
    (offsetExpr valExpr : YulExpr) :
    execIRStmtWithInternals contract fuel state
      (YulStmt.expr (YulExpr.call "mstore" [offsetExpr, valExpr])) =
        match execIRStmt fuel state
          (YulStmt.expr (YulExpr.call "mstore" [offsetExpr, valExpr])) with
        | .continue next => .continue next
        | .return value next => .return value next
        | .stop next => .stop next
        | .revert next => .revert next := by
  cases fuel with
  | zero =>
      simp [execIRStmtWithInternals, execIRStmt]
  | succ fuel =>
      cases hoffset : evalIRExpr state offsetExpr <;>
        cases hval : evalIRExpr state valExpr <;>
          simp [execIRStmtWithInternals, execIRStmt, evalIRExprs,
            evalIRExprsWithInternals_eq_evalIRExprs_of_no_internal contract hinternal,
            hoffset, hval]

/-- Helper-free helper-aware execution preserves legacy `revert` statement
semantics. -/
theorem execIRStmtWithInternals_eq_execIRStmt_revert_of_no_internal
    (contract : IRContract)
    (hinternal : contract.internalFunctions = [])
    (fuel : Nat) (state : IRState)
    (offsetExpr sizeExpr : YulExpr) :
    execIRStmtWithInternals contract fuel state
      (YulStmt.expr (YulExpr.call "revert" [offsetExpr, sizeExpr])) =
        match execIRStmt fuel state
          (YulStmt.expr (YulExpr.call "revert" [offsetExpr, sizeExpr])) with
        | .continue next => .continue next
        | .return value next => .return value next
        | .stop next => .stop next
        | .revert next => .revert next := by
  cases fuel with
  | zero =>
      simp [execIRStmtWithInternals, execIRStmt]
  | succ fuel =>
      cases hoffset : evalIRExpr state offsetExpr <;>
        cases hsize : evalIRExpr state sizeExpr <;>
          simp [execIRStmtWithInternals, execIRStmt, evalIRExprs,
            evalIRExprsWithInternals_eq_evalIRExprs_of_no_internal contract hinternal,
            hoffset, hsize]

/-- Helper-free helper-aware execution preserves legacy `return` statement
semantics. -/
theorem execIRStmtWithInternals_eq_execIRStmt_return_of_no_internal
    (contract : IRContract)
    (hinternal : contract.internalFunctions = [])
    (fuel : Nat) (state : IRState)
    (offsetExpr sizeExpr : YulExpr) :
    execIRStmtWithInternals contract fuel state
      (YulStmt.expr (YulExpr.call "return" [offsetExpr, sizeExpr])) =
        match execIRStmt fuel state
          (YulStmt.expr (YulExpr.call "return" [offsetExpr, sizeExpr])) with
        | .continue next => .continue next
        | .return value next => .return value next
        | .stop next => .stop next
        | .revert next => .revert next := by
  cases fuel with
  | zero =>
      simp [execIRStmtWithInternals, execIRStmt]
  | succ fuel =>
      cases hoffset : evalIRExpr state offsetExpr with
      | none =>
          cases hsize : evalIRExpr state sizeExpr <;>
            simp [execIRStmtWithInternals, execIRStmt, evalIRExprs,
              evalIRExprsWithInternals_eq_evalIRExprs_of_no_internal contract hinternal,
              hoffset, hsize]
      | some offset =>
          cases hsize : evalIRExpr state sizeExpr with
          | none =>
              simp [execIRStmtWithInternals, execIRStmt, evalIRExprs,
                evalIRExprsWithInternals_eq_evalIRExprs_of_no_internal contract hinternal,
                hoffset, hsize]
          | some size =>
              by_cases h32 : size = 32 <;>
                simp [execIRStmtWithInternals, execIRStmt, evalIRExprs,
                  evalIRExprsWithInternals_eq_evalIRExprs_of_no_internal contract hinternal,
                  hoffset, hsize, h32]

/-- Helper-free helper-aware execution preserves legacy `stop` statement
semantics. -/
theorem execIRStmtWithInternals_eq_execIRStmt_stop_of_no_internal
    (contract : IRContract)
    (_hinternal : contract.internalFunctions = [])
    (fuel : Nat) (state : IRState) :
    execIRStmtWithInternals contract fuel state
      (YulStmt.expr (YulExpr.call "stop" [])) =
        match execIRStmt fuel state
          (YulStmt.expr (YulExpr.call "stop" [])) with
        | .continue next => .continue next
        | .return value next => .return value next
        | .stop next => .stop next
        | .revert next => .revert next := by
  cases fuel <;> simp [execIRStmtWithInternals, execIRStmt]

/-- The helper-free conservative-extension interface is now discharged for the
expression layer: both single-expression and expression-list helper-aware
evaluation collapse definitionally to the legacy helper-free evaluator when the
runtime contract has no internal helpers. -/
theorem interpretIRWithInternalsZeroConservativeExtensionExprInterfaces
    (contract : IRContract) :
    (∀ (_hinternal : contract.internalFunctions = []) fuel state expr,
        evalIRExprWithInternals contract fuel state expr =
          match evalIRExpr state expr with
          | some value => .value value state
          | none => .revert state) ∧
    (∀ (_hinternal : contract.internalFunctions = []) fuel state exprs,
        evalIRExprsWithInternals contract fuel state exprs =
          match evalIRExprs state exprs with
          | some values => .values values state
          | none => .revert state) := by
  exact ⟨evalIRExprWithInternals_eq_evalIRExpr_of_no_internal contract,
    evalIRExprsWithInternals_eq_evalIRExprs_of_no_internal contract⟩

/-- Helper-free helper-aware execution preserves legacy `sstore` statement
semantics on both plain storage slots and mapping-slot addressing. -/
theorem execIRStmtWithInternals_eq_execIRStmt_sstore_of_no_internal
    (contract : IRContract)
    (hinternal : contract.internalFunctions = [])
    (fuel : Nat) (state : IRState)
    (slotExpr valExpr : YulExpr) :
    execIRStmtWithInternals contract fuel state
      (YulStmt.expr (YulExpr.call "sstore" [slotExpr, valExpr])) =
        match execIRStmt fuel state
          (YulStmt.expr (YulExpr.call "sstore" [slotExpr, valExpr])) with
        | .continue next => .continue next
        | .return value next => .return value next
        | .stop next => .stop next
        | .revert next => .revert next := by
  cases fuel with
  | zero =>
      simp [execIRStmtWithInternals, execIRStmt]
  | succ fuel =>
      cases slotExpr with
      | lit n =>
          cases hslot : evalIRExpr state (.lit n) <;>
            cases hval : evalIRExpr state valExpr <;>
              simp [execIRStmtWithInternals, execIRStmt, evalIRExprs,
                evalIRExprsWithInternals_eq_evalIRExprs_of_no_internal contract hinternal,
                hslot, hval]
      | hex n =>
          cases hslot : evalIRExpr state (.hex n) <;>
            cases hval : evalIRExpr state valExpr <;>
              simp [execIRStmtWithInternals, execIRStmt, evalIRExprs,
                evalIRExprsWithInternals_eq_evalIRExprs_of_no_internal contract hinternal,
                hslot, hval]
      | str s =>
          cases hslot : evalIRExpr state (.str s) <;>
            cases hval : evalIRExpr state valExpr <;>
              simp [execIRStmtWithInternals, execIRStmt, evalIRExprs,
                evalIRExprsWithInternals_eq_evalIRExprs_of_no_internal contract hinternal,
                hslot, hval]
      | ident name =>
          cases hslot : evalIRExpr state (.ident name) <;>
            cases hval : evalIRExpr state valExpr <;>
              simp [execIRStmtWithInternals, execIRStmt, evalIRExprs,
                evalIRExprsWithInternals_eq_evalIRExprs_of_no_internal contract hinternal,
                hslot, hval]
      | call func args =>
          cases args with
          | nil =>
              cases hslot : evalIRExpr state (.call func []) <;>
                cases hval : evalIRExpr state valExpr <;>
                  simp [execIRStmtWithInternals, execIRStmt, evalIRExprs,
                    evalIRExprsWithInternals_eq_evalIRExprs_of_no_internal contract hinternal,
                    hslot, hval]
          | cons arg rest =>
              cases rest with
              | nil =>
                  cases hslot : evalIRExpr state (.call func [arg]) <;>
                    cases hval : evalIRExpr state valExpr <;>
                      simp [execIRStmtWithInternals, execIRStmt, evalIRExprs,
                        evalIRExprsWithInternals_eq_evalIRExprs_of_no_internal contract hinternal,
                        hslot, hval]
              | cons arg2 rest =>
                  cases rest with
                  | nil =>
                      by_cases hfunc : func = "mappingSlot"
                      · subst hfunc
                        cases hbase : evalIRExpr state arg <;>
                          cases hkey : evalIRExpr state arg2 <;>
                            cases hval : evalIRExpr state valExpr <;>
                              simp [execIRStmtWithInternals, execIRStmt,
                                evalIRExprWithInternals_eq_evalIRExpr_of_no_internal contract hinternal,
                                hbase, hkey, hval]
                      · cases hslot : evalIRExpr state (.call func [arg, arg2]) <;>
                          cases hval : evalIRExpr state valExpr <;>
                            simp [execIRStmtWithInternals, execIRStmt, evalIRExprs,
                              evalIRExprsWithInternals_eq_evalIRExprs_of_no_internal contract hinternal,
                              hslot, hval, hfunc]
                  | cons arg3 rest =>
                      cases hslot : evalIRExpr state (.call func (arg :: arg2 :: arg3 :: rest)) <;>
                        cases hval : evalIRExpr state valExpr <;>
                          simp [execIRStmtWithInternals, execIRStmt, evalIRExprs,
                            evalIRExprsWithInternals_eq_evalIRExprs_of_no_internal contract hinternal,
                            hslot, hval]

/-- The remaining expr-statement helper-free conservative-extension seam is now
closed: dedicated builtin statement forms are handled by direct lemmas, and all
other expr statements collapse to the already-proved helper-free evaluator
equality. -/
theorem execIRStmtWithInternals_eq_execIRStmt_expr_of_no_internal
    (contract : IRContract) :
    contract.internalFunctions = [] →
      ∀ fuel state expr,
        execIRStmtWithInternals contract fuel state (.expr expr) =
          match execIRStmt fuel state (.expr expr) with
          | .continue next => .continue next
          | .return value next => .return value next
          | .stop next => .stop next
          | .revert next => .revert next
  | hinternal, fuel, state, expr => by
      cases fuel with
      | zero =>
          simp [execIRStmtWithInternals, execIRStmt]
      | succ fuel =>
          cases expr with
          | lit n =>
              cases hlit : evalIRExpr state (.lit n) <;>
                simp [execIRStmtWithInternals, execIRStmt,
                  evalIRExprWithInternals_eq_evalIRExpr_of_no_internal contract hinternal,
                  hlit]
          | hex n =>
              cases hhex : evalIRExpr state (.hex n) <;>
                simp [execIRStmtWithInternals, execIRStmt,
                  evalIRExprWithInternals_eq_evalIRExpr_of_no_internal contract hinternal,
                  hhex]
          | str s =>
              cases hstr : evalIRExpr state (.str s) <;>
                simp [execIRStmtWithInternals, execIRStmt,
                  evalIRExprWithInternals_eq_evalIRExpr_of_no_internal contract hinternal,
                  hstr]
          | ident name =>
              cases hident : state.getVar name <;>
                simp [execIRStmtWithInternals, execIRStmt, evalIRExpr,
                  evalIRExprWithInternals_eq_evalIRExpr_of_no_internal contract hinternal,
                  hident]
          | call func args =>
              cases args with
              | nil =>
                  by_cases hstop : func = "stop"
                  · subst hstop
                    simpa using execIRStmtWithInternals_eq_execIRStmt_stop_of_no_internal
                      contract hinternal (Nat.succ fuel) state
                  · cases hcall : evalIRExpr state (.call func []) <;>
                      simp [execIRStmtWithInternals, execIRStmt,
                        evalIRExprWithInternals_eq_evalIRExpr_of_no_internal contract hinternal,
                        hstop, hcall]
              | cons arg rest =>
                  cases rest with
                  | nil =>
                      cases hcall : evalIRExpr state (.call func [arg]) <;>
                        simp [execIRStmtWithInternals, execIRStmt,
                          evalIRExprWithInternals_eq_evalIRExpr_of_no_internal contract hinternal,
                          hcall]
                  | cons arg2 rest =>
                      cases rest with
                      | nil =>
                          by_cases hsstore : func = "sstore"
                          · subst hsstore
                            simpa using execIRStmtWithInternals_eq_execIRStmt_sstore_of_no_internal
                              contract hinternal (Nat.succ fuel) state arg arg2
                          · by_cases hmstore : func = "mstore"
                            · subst hmstore
                              simpa using execIRStmtWithInternals_eq_execIRStmt_mstore_of_no_internal
                                contract hinternal (Nat.succ fuel) state arg arg2
                            · by_cases hrevert : func = "revert"
                              · subst hrevert
                                simpa using execIRStmtWithInternals_eq_execIRStmt_revert_of_no_internal
                                  contract hinternal (Nat.succ fuel) state arg arg2
                              · by_cases hreturn : func = "return"
                                · subst hreturn
                                  simpa using execIRStmtWithInternals_eq_execIRStmt_return_of_no_internal
                                    contract hinternal (Nat.succ fuel) state arg arg2
                                · cases hcall : evalIRExpr state (.call func [arg, arg2]) <;>
                                    simp [execIRStmtWithInternals, execIRStmt,
                                      evalIRExprWithInternals_eq_evalIRExpr_of_no_internal contract hinternal,
                                      hsstore, hmstore, hrevert, hreturn, hcall]
                      | cons arg3 rest =>
                          cases hcall : evalIRExpr state (.call func (arg :: arg2 :: arg3 :: rest)) <;>
                            simp [execIRStmtWithInternals, execIRStmt,
                              evalIRExprWithInternals_eq_evalIRExpr_of_no_internal contract hinternal,
                              hcall]

/-- Statement-list compatibility is also derivable from expression-statement
compatibility alone on the legacy-compatible external subset. This collapses the
remaining compiled-side helper-free retarget seam to one semantic field instead
of separate stmt, `if`, `block`, and stmt-list obligations. -/
theorem execIRStmtsWithInternals_eq_execIRStmts_of_exprCompatibility
    (contract : IRContract)
    (hexpr :
      contract.internalFunctions = [] →
        ∀ fuel state expr,
          execIRStmtWithInternals contract fuel state (.expr expr) =
            match execIRStmt fuel state (.expr expr) with
            | .continue next => .continue next
            | .return value next => .return value next
            | .stop next => .stop next
            | .revert next => .revert next) :
    contract.internalFunctions = [] →
      ∀ fuel state stmts,
        LegacyCompatibleExternalStmtList stmts →
          execIRStmtsWithInternals contract fuel state stmts =
            match execIRStmts fuel state stmts with
            | .continue next => .continue next
            | .return value next => .return value next
            | .stop next => .stop next
            | .revert next => .revert next
  | hinternal, fuel, state, stmts, hlegacy => by
      induction hlegacy generalizing fuel state with
      | nil =>
          cases fuel <;> simp [execIRStmtsWithInternals, execIRStmts]
      | comment msg rest hrest ih =>
          cases fuel with
          | zero =>
              simp [execIRStmtsWithInternals, execIRStmts]
          | succ fuel =>
              have hhead :
                  execIRStmtWithInternals contract fuel state (.comment msg) =
                    match execIRStmt fuel state (.comment msg) with
                    | .continue next => .continue next
                    | .return value next => .return value next
                    | .stop next => .stop next
                    | .revert next => .revert next := by
                cases fuel <;> simp [execIRStmtWithInternals, execIRStmt]
              rw [execIRStmtsWithInternals, execIRStmts, hhead]
              cases hstep : execIRStmt fuel state (.comment msg) <;>
                simp [ih]
      | let_ name value rest hrest ih =>
          cases fuel with
          | zero =>
              simp [execIRStmtsWithInternals, execIRStmts]
          | succ fuel =>
              have hhead :
                  execIRStmtWithInternals contract fuel state (.let_ name value) =
                    match execIRStmt fuel state (.let_ name value) with
                    | .continue next => .continue next
                    | .return value next => .return value next
                    | .stop next => .stop next
                    | .revert next => .revert next := by
                cases fuel with
                | zero =>
                    simp [execIRStmtWithInternals, execIRStmt]
                | succ fuel =>
                    cases hval : evalIRExpr state value <;>
                      simp [execIRStmtWithInternals, execIRStmt,
                        evalIRExprWithInternals_eq_evalIRExpr_of_no_internal contract hinternal, hval]
              rw [execIRStmtsWithInternals, execIRStmts, hhead]
              cases hstep : execIRStmt fuel state (.let_ name value) <;>
                simp [ih]
      | assign name value rest hrest ih =>
          cases fuel with
          | zero =>
              simp [execIRStmtsWithInternals, execIRStmts]
          | succ fuel =>
              have hhead :
                  execIRStmtWithInternals contract fuel state (.assign name value) =
                    match execIRStmt fuel state (.assign name value) with
                    | .continue next => .continue next
                    | .return value next => .return value next
                    | .stop next => .stop next
                    | .revert next => .revert next := by
                cases fuel with
                | zero =>
                    simp [execIRStmtWithInternals, execIRStmt]
                | succ fuel =>
                    cases hval : evalIRExpr state value <;>
                      simp [execIRStmtWithInternals, execIRStmt,
                        evalIRExprWithInternals_eq_evalIRExpr_of_no_internal contract hinternal, hval]
              rw [execIRStmtsWithInternals, execIRStmts, hhead]
              cases hstep : execIRStmt fuel state (.assign name value) <;>
                simp [ih]
      | expr value rest hrest ih =>
          cases fuel with
          | zero =>
              simp [execIRStmtsWithInternals, execIRStmts]
          | succ fuel =>
              have hhead := hexpr hinternal fuel state value
              rw [execIRStmtsWithInternals, execIRStmts, hhead]
              cases hstep : execIRStmt fuel state (.expr value) <;>
                simp [ih]
      | if_ cond body rest hbody hrest ihBody ihRest =>
          cases fuel with
          | zero =>
              simp [execIRStmtsWithInternals, execIRStmts]
          | succ fuel =>
              have hhead :
                  execIRStmtWithInternals contract fuel state (.if_ cond body) =
                    match execIRStmt fuel state (.if_ cond body) with
                    | .continue next => .continue next
                    | .return value next => .return value next
                    | .stop next => .stop next
                    | .revert next => .revert next := by
                cases fuel with
                | zero =>
                    simp [execIRStmtWithInternals, execIRStmt]
                | succ fuel =>
                    rw [execIRStmtWithInternals, execIRStmt]
                    rw [evalIRExprWithInternals_eq_evalIRExpr_of_no_internal contract hinternal fuel state cond]
                    cases hcond : evalIRExpr state cond with
                    | none =>
                        simp
                    | some condValue =>
                        by_cases hnonzero : condValue ≠ 0
                        · simp [hnonzero, ihBody fuel state]
                        · simp [hnonzero]
              rw [execIRStmtsWithInternals, execIRStmts, hhead]
              cases hstep : execIRStmt fuel state (.if_ cond body) <;>
                simp [ihRest]
      | block body rest hbody hrest ihBody ihRest =>
          cases fuel with
          | zero =>
              simp [execIRStmtsWithInternals, execIRStmts]
          | succ fuel =>
              have hhead :
                  execIRStmtWithInternals contract fuel state (.block body) =
                    match execIRStmt fuel state (.block body) with
                    | .continue next => .continue next
                    | .return value next => .return value next
                    | .stop next => .stop next
                    | .revert next => .revert next := by
                cases fuel with
                | zero =>
                    simp [execIRStmtWithInternals, execIRStmt]
                | succ fuel =>
                    simpa [execIRStmtWithInternals, execIRStmt] using ihBody fuel state
              rw [execIRStmtsWithInternals, execIRStmts, hhead]
              cases hstep : execIRStmt fuel state (.block body) <;>
                simp [ihRest]
      | funcDef name params rets body rest hbody hrest ihBody ihRest =>
          cases fuel with
          | zero =>
              simp [execIRStmtsWithInternals, execIRStmts]
          | succ fuel =>
              have hhead :
                  execIRStmtWithInternals contract fuel state (.funcDef name params rets body) =
                    match execIRStmt fuel state (.funcDef name params rets body) with
                    | .continue next => .continue next
                    | .return value next => .return value next
                    | .stop next => .stop next
                    | .revert next => .revert next := by
                simp [execIRStmtWithInternals, execIRStmt]
              rw [execIRStmtsWithInternals, execIRStmts, hhead]
              cases hstep : execIRStmt fuel state (.funcDef name params rets body) <;>
                simp [ihRest]

/-- Single-statement compatibility now follows mechanically from the list theorem:
a compatible stmt is just a compatible singleton stmt list. -/
theorem execIRStmtWithInternals_eq_execIRStmt_of_exprCompatibility
    (contract : IRContract)
    (hexpr :
      contract.internalFunctions = [] →
        ∀ fuel state expr,
          execIRStmtWithInternals contract fuel state (.expr expr) =
            match execIRStmt fuel state (.expr expr) with
            | .continue next => .continue next
            | .return value next => .return value next
            | .stop next => .stop next
            | .revert next => .revert next) :
    contract.internalFunctions = [] →
      ∀ fuel state stmt,
        LegacyCompatibleExternalStmt stmt →
          execIRStmtWithInternals contract fuel state stmt =
            match execIRStmt fuel state stmt with
            | .continue next => .continue next
            | .return value next => .return value next
            | .stop next => .stop next
            | .revert next => .revert next := by
  intro hinternal fuel state stmt hstmt
  have hsingleton :=
    execIRStmtsWithInternals_eq_execIRStmts_of_exprCompatibility
      contract hexpr hinternal (fuel + 1) state [stmt] hstmt
  cases hwith : execIRStmtWithInternals contract fuel state stmt <;>
    cases hlegacy : execIRStmt fuel state stmt <;>
      simp [execIRStmtsWithInternals, execIRStmts, hwith, hlegacy] at hsingleton ⊢ <;>
      simpa using hsingleton

/-- The remaining single-statement helper-free conservative-extension seam is now
packaged as an explicit one-field interface: the real semantic work sits in
`YulStmt.expr`, while `if`, `block`, stmt-list, function, dispatch, and
contract transport are already derivable compositionally on the same
legacy-compatible subset. -/
structure InterpretIRWithInternalsZeroConservativeExtensionStmtSubgoals
    (contract : IRContract) where
  exprCompatibility :
    contract.internalFunctions = [] →
      ∀ fuel state expr,
        execIRStmtWithInternals contract fuel state (.expr expr) =
          match execIRStmt fuel state (.expr expr) with
          | .continue next => .continue next
          | .return value next => .return value next
          | .stop next => .stop next
          | .revert next => .revert next

/-- The old prose-only description of the remaining stmt blocker is now a real
proof interface object. Filling this one field is sufficient to recover the full
single-statement compatibility theorem. -/
theorem execIRStmtWithInternals_eq_execIRStmt_of_stmtSubgoals
    (contract : IRContract)
    (hsubgoals :
      InterpretIRWithInternalsZeroConservativeExtensionStmtSubgoals contract) :
    contract.internalFunctions = [] →
      ∀ fuel state stmt,
        LegacyCompatibleExternalStmt stmt →
          execIRStmtWithInternals contract fuel state stmt =
            match execIRStmt fuel state stmt with
            | .continue next => .continue next
            | .return value next => .return value next
            | .stop next => .stop next
            | .revert next => .revert next := by
  exact execIRStmtWithInternals_eq_execIRStmt_of_exprCompatibility
    contract hsubgoals.exprCompatibility


/-- Statement-list compatibility is mechanically derivable from single-statement
compatibility: once the head step is known to coincide, the remaining list proof
is just tail composition on the same fuel/state. This isolates the compiled-side
helper retarget blocker to the stmt layer rather than the whole stmt-list layer. -/
theorem execIRStmtsWithInternals_eq_execIRStmts_of_stmtCompatibility
    (contract : IRContract)
    (hstmt :
      contract.internalFunctions = [] →
        ∀ fuel state stmt,
          LegacyCompatibleExternalStmt stmt →
            execIRStmtWithInternals contract fuel state stmt =
              match execIRStmt fuel state stmt with
              | .continue next => .continue next
              | .return value next => .return value next
              | .stop next => .stop next
              | .revert next => .revert next) :
    contract.internalFunctions = [] →
      ∀ fuel state stmts,
        LegacyCompatibleExternalStmtList stmts →
          execIRStmtsWithInternals contract fuel state stmts =
            match execIRStmts fuel state stmts with
            | .continue next => .continue next
            | .return value next => .return value next
            | .stop next => .stop next
            | .revert next => .revert next := by
  intro hinternal fuel state stmts hlegacy
  induction hlegacy generalizing fuel state with
  | nil =>
      cases fuel <;> simp [execIRStmtsWithInternals, execIRStmts]
  | comment msg rest hrest ih =>
      cases fuel with
      | zero =>
          simp [execIRStmtsWithInternals, execIRStmts]
      | succ fuel =>
          have hhead :=
            hstmt hinternal fuel state (.comment msg)
              (LegacyCompatibleExternalStmtList.comment msg [] LegacyCompatibleExternalStmtList.nil)
          rw [execIRStmtsWithInternals, execIRStmts, hhead]
          cases hstep : execIRStmt fuel state (.comment msg) <;>
            simp [ih]
  | let_ name value rest hrest ih =>
      cases fuel with
      | zero =>
          simp [execIRStmtsWithInternals, execIRStmts]
      | succ fuel =>
          have hhead :=
            hstmt hinternal fuel state (.let_ name value)
              (LegacyCompatibleExternalStmtList.let_ name value [] LegacyCompatibleExternalStmtList.nil)
          rw [execIRStmtsWithInternals, execIRStmts, hhead]
          cases hstep : execIRStmt fuel state (.let_ name value) <;>
            simp [ih]
  | assign name value rest hrest ih =>
      cases fuel with
      | zero =>
          simp [execIRStmtsWithInternals, execIRStmts]
      | succ fuel =>
          have hhead :=
            hstmt hinternal fuel state (.assign name value)
              (LegacyCompatibleExternalStmtList.assign name value [] LegacyCompatibleExternalStmtList.nil)
          rw [execIRStmtsWithInternals, execIRStmts, hhead]
          cases hstep : execIRStmt fuel state (.assign name value) <;>
            simp [ih]
  | expr value rest hrest ih =>
      cases fuel with
      | zero =>
          simp [execIRStmtsWithInternals, execIRStmts]
      | succ fuel =>
          have hhead :=
            hstmt hinternal fuel state (.expr value)
              (LegacyCompatibleExternalStmtList.expr value [] LegacyCompatibleExternalStmtList.nil)
          rw [execIRStmtsWithInternals, execIRStmts, hhead]
          cases hstep : execIRStmt fuel state (.expr value) <;>
            simp [ih]
  | if_ cond body rest hbody hrest ihBody ihRest =>
      cases fuel with
      | zero =>
          simp [execIRStmtsWithInternals, execIRStmts]
      | succ fuel =>
          have hhead :=
            hstmt hinternal fuel state (.if_ cond body)
              (LegacyCompatibleExternalStmtList.if_ cond body [] hbody LegacyCompatibleExternalStmtList.nil)
          rw [execIRStmtsWithInternals, execIRStmts, hhead]
          cases hstep : execIRStmt fuel state (.if_ cond body) <;>
            simp [ihRest]
  | block body rest hbody hrest ihBody ihRest =>
      cases fuel with
      | zero =>
          simp [execIRStmtsWithInternals, execIRStmts]
      | succ fuel =>
          have hhead :=
            hstmt hinternal fuel state (.block body)
              (LegacyCompatibleExternalStmtList.block body [] hbody LegacyCompatibleExternalStmtList.nil)
          rw [execIRStmtsWithInternals, execIRStmts, hhead]
          cases hstep : execIRStmt fuel state (.block body) <;>
            simp [ihRest]
  | funcDef name params rets body rest hbody hrest ihBody ihRest =>
      cases fuel with
      | zero =>
          simp [execIRStmtsWithInternals, execIRStmts]
      | succ fuel =>
          have hhead :=
            hstmt hinternal fuel state (.funcDef name params rets body)
              (LegacyCompatibleExternalStmtList.funcDef
                name params rets body [] hbody LegacyCompatibleExternalStmtList.nil)
          rw [execIRStmtsWithInternals, execIRStmts, hhead]
          cases hstep : execIRStmt fuel state (.funcDef name params rets body) <;>
            simp [ihRest]

/-- Once statement-list compatibility is proved, the function-level compatibility
field in `InterpretIRWithInternalsZeroConservativeExtensionInterfaces` is just
plumbing: both interpreters initialize parameters identically and run the same
fuel budget when `helperFuel = 0`. This keeps the remaining compiled-side blocker
focused on stmt / stmt-list compatibility instead of re-proving function setup. -/
theorem execIRFunctionWithInternals_eq_execIRFunction_of_stmtListCompatibility
    (contract : IRContract)
    (hstmtList :
      ∀ (_hinternal : contract.internalFunctions = []) fuel state stmts,
        LegacyCompatibleExternalStmtList stmts →
          execIRStmtsWithInternals contract fuel state stmts =
            match execIRStmts fuel state stmts with
            | .continue next => .continue next
            | .return value next => .return value next
            | .stop next => .stop next
            | .revert next => .revert next) :
    contract.internalFunctions = [] →
      ∀ fn args initialState,
        LegacyCompatibleExternalStmtList fn.body →
          execIRFunctionWithInternals contract 0 fn args initialState =
            execIRFunction fn args initialState := by
  intro hinternal fn args initialState hbody
  let stateWithParams :=
    fn.params.zip args |>.foldl (fun s (p, v) => s.setVar p.name v) initialState
  rw [execIRFunctionWithInternals, execIRFunction]
  rw [hstmtList hinternal (sizeOf fn.body + 1) stateWithParams fn.body hbody]
  cases execIRStmts (sizeOf fn.body + 1) stateWithParams fn.body <;> rfl

/-- The single-statement compatibility field is also just plumbing once the
statement-list theorem is available: a compatible statement is exactly a
singleton compatible statement list. This keeps the remaining blocker focused on
the list theorem rather than splitting effort across equivalent surfaces. -/
theorem execIRStmtWithInternals_eq_execIRStmt_of_stmtListCompatibility
    (contract : IRContract)
    (hstmtList :
      ∀ (_hinternal : contract.internalFunctions = []) fuel state stmts,
        LegacyCompatibleExternalStmtList stmts →
          execIRStmtsWithInternals contract fuel state stmts =
            match execIRStmts fuel state stmts with
            | .continue next => .continue next
            | .return value next => .return value next
            | .stop next => .stop next
            | .revert next => .revert next) :
    contract.internalFunctions = [] →
      ∀ fuel state stmt,
        LegacyCompatibleExternalStmt stmt →
          execIRStmtWithInternals contract fuel state stmt =
            match execIRStmt fuel state stmt with
            | .continue next => .continue next
            | .return value next => .return value next
            | .stop next => .stop next
            | .revert next => .revert next := by
  intro hinternal fuel state stmt hstmt
  have hsingleton :=
    hstmtList hinternal (fuel + 1) state [stmt] hstmt
  cases hwith : execIRStmtWithInternals contract fuel state stmt <;>
    cases hlegacy : execIRStmt fuel state stmt <;>
      simp [execIRStmtsWithInternals, execIRStmts, hwith, hlegacy] at hsingleton ⊢ <;>
      simpa using hsingleton

/-- The helper-free conservative-extension interface is now machine-assembled from
the already-proved expr layer plus a single stmt compatibility theorem. This
makes the remaining compiled-side blocker literally one interface field rather
than a loose collection of downstream obligations. -/
theorem interpretIRWithInternalsZeroConservativeExtensionInterfaces_of_stmtCompatibility
    (contract : IRContract)
    (hstmt :
      contract.internalFunctions = [] →
        ∀ fuel state stmt,
          LegacyCompatibleExternalStmt stmt →
            execIRStmtWithInternals contract fuel state stmt =
              match execIRStmt fuel state stmt with
              | .continue next => .continue next
              | .return value next => .return value next
              | .stop next => .stop next
              | .revert next => .revert next) :
    InterpretIRWithInternalsZeroConservativeExtensionInterfaces contract := by
  refine
    { exprCompatibility := evalIRExprWithInternals_eq_evalIRExpr_of_no_internal contract
      exprListCompatibility := evalIRExprsWithInternals_eq_evalIRExprs_of_no_internal contract
      stmtCompatibility := hstmt
      stmtListCompatibility :=
        execIRStmtsWithInternals_eq_execIRStmts_of_stmtCompatibility contract hstmt
      functionCompatibility :=
        execIRFunctionWithInternals_eq_execIRFunction_of_stmtListCompatibility contract
          (execIRStmtsWithInternals_eq_execIRStmts_of_stmtCompatibility contract hstmt) }

/-- Shared transaction-context initialization used by both legacy and helper-aware
top-level IR interpreters. Making this explicit removes boilerplate from the
remaining conservative-extension proof target. -/
def applyIRTransactionContext (tx : IRTransaction) (initialState : IRState) : IRState :=
  { initialState with
    sender := tx.sender
    msgValue := tx.msgValue
    thisAddress := tx.thisAddress
    blockTimestamp := tx.blockTimestamp
    blockNumber := tx.blockNumber
    chainId := tx.chainId
    blobBaseFee := tx.blobBaseFee
    calldata := tx.args
    selector := tx.functionSelector }

/-- Dispatch-local restatement of the helper-free runtime-contract boundary.
This is equivalent to `LegacyCompatibleRuntimeContract`, but packages the
remaining compiled-side retarget goal around the actually selected external
function instead of quantifying over the whole function list at each proof step. -/
def LegacyCompatibleRuntimeDispatch (contract : IRContract) : Prop :=
  contract.internalFunctions = [] ∧
    ∀ (tx : IRTransaction) (fn : IRFunction),
      contract.functions.find? (·.selector == tx.functionSelector) = some fn →
        LegacyCompatibleExternalStmtList fn.body

/-- The first compiled-side retarget theorem can be decomposed into a dispatch-local
function step plus the already-shared transaction-context setup. This isolates the
remaining proof obligation to the selected external function. -/
def InterpretIRWithInternalsZeroConservativeExtensionDispatchGoal
    (contract : IRContract) : Prop :=
  LegacyCompatibleRuntimeDispatch contract →
    ∀ (tx : IRTransaction) initialState (fn : IRFunction),
      contract.functions.find? (·.selector == tx.functionSelector) = some fn →
      execIRFunctionWithInternals contract 0 fn tx.args (applyIRTransactionContext tx initialState) =
        execIRFunction fn tx.args (applyIRTransactionContext tx initialState)

theorem legacyCompatibleRuntimeDispatch_of_legacyCompatibleRuntimeContract
    (contract : IRContract) :
    LegacyCompatibleRuntimeContract contract →
      LegacyCompatibleRuntimeDispatch contract := by
  intro hlegacy
  rcases hlegacy with ⟨hinternal, hfunctions⟩
  refine ⟨hinternal, ?_⟩
  intro tx fn hfind
  exact hfunctions fn (List.mem_of_find?_eq_some hfind)

/-- Once stmt-list compatibility is proved, the dispatch-local theorem is only
runtime-contract bookkeeping: helper-free dispatch already selects a legacy-
compatible external body, and function compatibility collapses the selected
helper-aware execution to the legacy helper-free one. -/
theorem interpretIRWithInternalsZeroConservativeExtensionDispatchGoal_of_stmtListCompatibility
    (contract : IRContract)
    (hstmtList :
      ∀ (_hinternal : contract.internalFunctions = []) fuel state stmts,
        LegacyCompatibleExternalStmtList stmts →
          execIRStmtsWithInternals contract fuel state stmts =
            match execIRStmts fuel state stmts with
            | .continue next => .continue next
            | .return value next => .return value next
            | .stop next => .stop next
            | .revert next => .revert next) :
    InterpretIRWithInternalsZeroConservativeExtensionDispatchGoal contract := by
  intro hdispatch tx initialState fn hfind
  rcases hdispatch with ⟨hinternal, hcompatible⟩
  exact execIRFunctionWithInternals_eq_execIRFunction_of_stmtListCompatibility
    contract hstmtList hinternal fn tx.args (applyIRTransactionContext tx initialState)
    (hcompatible tx fn hfind)

/-- Once the selected-function compatibility theorem is available, the public
contract-level helper-free conservative-extension goal follows directly. This
packages the remaining compiled-side blocker as one dispatch-local theorem plus
the already-explicit runtime-boundary conversion. -/
theorem interpretIRWithInternalsZeroConservativeExtensionGoal_of_dispatchGoal
    (contract : IRContract) :
    InterpretIRWithInternalsZeroConservativeExtensionDispatchGoal contract →
      InterpretIRWithInternalsZeroConservativeExtensionGoal contract := by
  intro hdispatch
  intro hlegacy tx initialState
  let stateWithTx := applyIRTransactionContext tx initialState
  cases hfind : contract.functions.find? (·.selector == tx.functionSelector) with
  | none =>
      simp [interpretIRWithInternals, interpretIR, hfind]
  | some fn =>
      have hdispatchCompat :=
        hdispatch
          (legacyCompatibleRuntimeDispatch_of_legacyCompatibleRuntimeContract contract hlegacy)
          tx initialState fn hfind
      simp [interpretIRWithInternals, interpretIR, hfind]
      split
      · exact hdispatchCompat
      · rfl

/-- After the preceding reductions, the first compiled-side helper retarget
theorem is equivalent to proving the stmt-list compatibility field alone. The
stmt, function, dispatch-local, and contract-level layers are all now composed
from that one surface without changing theorem shape or trusted assumptions. -/
theorem interpretIRWithInternalsZeroConservativeExtensionGoal_of_stmtListCompatibility
    (contract : IRContract)
    (hstmtList :
      ∀ (_hinternal : contract.internalFunctions = []) fuel state stmts,
        LegacyCompatibleExternalStmtList stmts →
          execIRStmtsWithInternals contract fuel state stmts =
            match execIRStmts fuel state stmts with
            | .continue next => .continue next
            | .return value next => .return value next
            | .stop next => .stop next
            | .revert next => .revert next) :
    InterpretIRWithInternalsZeroConservativeExtensionGoal contract := by
  exact interpretIRWithInternalsZeroConservativeExtensionGoal_of_dispatchGoal contract
    (interpretIRWithInternalsZeroConservativeExtensionDispatchGoal_of_stmtListCompatibility
      contract hstmtList)

/-- With the list-composition theorem above, the remaining compiled-side helper-free
retarget blocker can be stated directly at the stmt layer. -/
theorem execIRFunctionWithInternals_eq_execIRFunction_of_stmtCompatibility
    (contract : IRContract)
    (hstmt :
      contract.internalFunctions = [] →
        ∀ fuel state stmt,
          LegacyCompatibleExternalStmt stmt →
            execIRStmtWithInternals contract fuel state stmt =
              match execIRStmt fuel state stmt with
              | .continue next => .continue next
              | .return value next => .return value next
              | .stop next => .stop next
              | .revert next => .revert next) :
    contract.internalFunctions = [] →
      ∀ fn args initialState,
        LegacyCompatibleExternalStmtList fn.body →
          execIRFunctionWithInternals contract 0 fn args initialState =
            execIRFunction fn args initialState := by
  apply execIRFunctionWithInternals_eq_execIRFunction_of_stmtListCompatibility
  exact execIRStmtsWithInternals_eq_execIRStmts_of_stmtCompatibility contract hstmt

/-- Dispatch-local conservative extension is also mechanical once single-statement
compatibility is available. -/
theorem interpretIRWithInternalsZeroConservativeExtensionDispatchGoal_of_stmtCompatibility
    (contract : IRContract)
    (hstmt :
      contract.internalFunctions = [] →
        ∀ fuel state stmt,
          LegacyCompatibleExternalStmt stmt →
            execIRStmtWithInternals contract fuel state stmt =
              match execIRStmt fuel state stmt with
              | .continue next => .continue next
              | .return value next => .return value next
              | .stop next => .stop next
              | .revert next => .revert next) :
    InterpretIRWithInternalsZeroConservativeExtensionDispatchGoal contract := by
  apply interpretIRWithInternalsZeroConservativeExtensionDispatchGoal_of_stmtListCompatibility
  exact execIRStmtsWithInternals_eq_execIRStmts_of_stmtCompatibility contract hstmt

/-- The public contract-level conservative-extension goal now also reduces to the
single-statement compatibility theorem. -/
theorem interpretIRWithInternalsZeroConservativeExtensionGoal_of_stmtCompatibility
    (contract : IRContract)
    (hstmt :
      contract.internalFunctions = [] →
        ∀ fuel state stmt,
          LegacyCompatibleExternalStmt stmt →
            execIRStmtWithInternals contract fuel state stmt =
              match execIRStmt fuel state stmt with
              | .continue next => .continue next
              | .return value next => .return value next
              | .stop next => .stop next
              | .revert next => .revert next) :
    InterpretIRWithInternalsZeroConservativeExtensionGoal contract := by
  apply interpretIRWithInternalsZeroConservativeExtensionGoal_of_stmtListCompatibility
  exact execIRStmtsWithInternals_eq_execIRStmts_of_stmtCompatibility contract hstmt

/-- The new stmt-subgoal object plugs directly into the already-existing helper-
free conservative-extension interface builder. This keeps the remaining proof
surface compositional instead of rediscovering the same assembly later. -/
theorem interpretIRWithInternalsZeroConservativeExtensionInterfaces_of_stmtSubgoals
    (contract : IRContract)
    (hsubgoals :
      InterpretIRWithInternalsZeroConservativeExtensionStmtSubgoals contract) :
    InterpretIRWithInternalsZeroConservativeExtensionInterfaces contract := by
  apply interpretIRWithInternalsZeroConservativeExtensionInterfaces_of_stmtCompatibility
  exact execIRStmtWithInternals_eq_execIRStmt_of_stmtSubgoals contract hsubgoals

/-- The contract-level helper-free conservative-extension goal also now reduces
to the named stmt-subgoal object. -/
theorem interpretIRWithInternalsZeroConservativeExtensionGoal_of_stmtSubgoals
    (contract : IRContract)
    (hsubgoals :
      InterpretIRWithInternalsZeroConservativeExtensionStmtSubgoals contract) :
    InterpretIRWithInternalsZeroConservativeExtensionGoal contract := by
  apply interpretIRWithInternalsZeroConservativeExtensionGoal_of_stmtCompatibility
  exact execIRStmtWithInternals_eq_execIRStmt_of_stmtSubgoals contract hsubgoals

/-- The remaining helper-free compiled-side stmt blocker is now closed on the
current runtime subset: the expr-statement compatibility field is discharged by
direct builtin lemmas plus the already-proved evaluator equality. -/
theorem interpretIRWithInternalsZeroConservativeExtensionStmtSubgoals_closed
    (contract : IRContract) :
    InterpretIRWithInternalsZeroConservativeExtensionStmtSubgoals contract := by
  refine
    { exprCompatibility := ?_ }
  exact execIRStmtWithInternals_eq_execIRStmt_expr_of_no_internal contract

/-- The full helper-free conservative-extension interface is now closed on the
current runtime subset. -/
theorem interpretIRWithInternalsZeroConservativeExtensionInterfaces_closed
    (contract : IRContract) :
    InterpretIRWithInternalsZeroConservativeExtensionInterfaces contract := by
  exact interpretIRWithInternalsZeroConservativeExtensionInterfaces_of_stmtSubgoals
    contract (interpretIRWithInternalsZeroConservativeExtensionStmtSubgoals_closed contract)

/-- The first compiled-side helper-aware retarget theorem is now proved on the
current helper-free runtime-contract boundary. -/
theorem interpretIRWithInternalsZeroConservativeExtensionGoal_closed
    (contract : IRContract) :
    InterpretIRWithInternalsZeroConservativeExtensionGoal contract := by
  exact interpretIRWithInternalsZeroConservativeExtensionGoal_of_stmtSubgoals
    contract (interpretIRWithInternalsZeroConservativeExtensionStmtSubgoals_closed contract)

/-! ## Disjointness-based conservative extension (widened fragment)

The following chain generalizes the `_closed` chain above by replacing the blanket
`contract.internalFunctions = []` requirement with per-body disjointness:
contracts **may** carry internal helper definitions as long as externally callable
function bodies do not reference them.  This widens the supported fragment from
"no internal functions at all" to "internal functions present but unused by
external call sites." -/

/-- A runtime contract whose externally callable function bodies are disjoint
from its internal function table.  Unlike `LegacyCompatibleRuntimeContract` this
does **not** require `contract.internalFunctions = []`. -/
def DisjointRuntimeContract (contract : IRContract) : Prop :=
  ∀ fn ∈ contract.functions,
    YulStmtListCallsDisjointFromInternalTable contract fn.body

/-- `LegacyCompatibleRuntimeContract` implies `DisjointRuntimeContract`: the
blanket "no internals" assumption trivially satisfies per-body disjointness. -/
theorem disjointRuntimeContract_of_legacyCompatibleRuntimeContract
    (contract : IRContract) :
    LegacyCompatibleRuntimeContract contract →
      DisjointRuntimeContract contract := by
  intro ⟨hinternal, hbodies⟩ fn hmem
  exact YulStmtListCallsDisjointFromInternalTable_of_internalFunctions_nil
    contract hinternal fn.body (hbodies fn hmem)

/-- Dispatch-local restatement of the disjointness boundary: once a function is
selected by the dispatcher, we only need disjointness for that single body. -/
def DisjointRuntimeDispatch (contract : IRContract) : Prop :=
  ∀ (tx : IRTransaction) (fn : IRFunction),
    contract.functions.find? (·.selector == tx.functionSelector) = some fn →
    YulStmtListCallsDisjointFromInternalTable contract fn.body

theorem disjointRuntimeDispatch_of_disjointRuntimeContract
    (contract : IRContract) :
    DisjointRuntimeContract contract →
      DisjointRuntimeDispatch contract := by
  intro hdisjoint tx fn hfind
  exact hdisjoint fn (List.mem_of_find?_eq_some hfind)

/-- Function-level conservative extension under body disjointness.  Since both
`execIRFunctionWithInternals contract 0` and `execIRFunction` use the same fuel
`sizeOf fn.body + 1` and parameterize identically, all that is needed is
stmt-list compatibility — which is exactly what
`execIRStmtsWithInternals_eq_execIRStmts_of_callsDisjoint` provides. -/
theorem execIRFunctionWithInternals_eq_execIRFunction_of_bodyCallsDisjoint
    (contract : IRContract) :
    ∀ fn args initialState,
      YulStmtListCallsDisjointFromInternalTable contract fn.body →
        execIRFunctionWithInternals contract 0 fn args initialState =
          execIRFunction fn args initialState := by
  intro fn args initialState hbody
  let stateWithParams :=
    fn.params.zip args |>.foldl (fun s (p, v) => s.setVar p.name v) initialState
  rw [execIRFunctionWithInternals, execIRFunction]
  rw [execIRStmtsWithInternals_eq_execIRStmts_of_callsDisjoint
    contract (sizeOf fn.body + 1) stateWithParams fn.body hbody]
  cases execIRStmts (sizeOf fn.body + 1) stateWithParams fn.body <;> rfl

/-- Top-level conservative extension goal under disjointness: on runtime
contracts whose external bodies are disjoint from the internal table, zero-helper-
fuel helper-aware interpretation coincides with public `interpretIR`.  This
strictly subsumes `InterpretIRWithInternalsZeroConservativeExtensionGoal`
(which additionally requires `contract.internalFunctions = []`). -/
def InterpretIRWithInternalsZeroConservativeExtensionGoalOfDisjoint
    (contract : IRContract) : Prop :=
  DisjointRuntimeContract contract →
    ∀ tx initialState,
      interpretIRWithInternals contract 0 tx initialState =
        interpretIR contract tx initialState

/-- The disjoint conservative extension goal is now proved: zero-helper-fuel
execution equals helper-free execution when every external body is disjoint from
the internal table. -/
theorem interpretIRWithInternalsZeroConservativeExtensionGoalOfDisjoint_closed
    (contract : IRContract) :
    InterpretIRWithInternalsZeroConservativeExtensionGoalOfDisjoint contract := by
  intro hdisjoint tx initialState
  let stateWithTx := applyIRTransactionContext tx initialState
  cases hfind : contract.functions.find? (·.selector == tx.functionSelector) with
  | none =>
      simp [interpretIRWithInternals, interpretIR, hfind]
  | some fn =>
      have hbody :=
        disjointRuntimeDispatch_of_disjointRuntimeContract contract hdisjoint
          tx fn hfind
      have hfnEq :=
        execIRFunctionWithInternals_eq_execIRFunction_of_bodyCallsDisjoint
          contract fn tx.args stateWithTx hbody
      simp [interpretIRWithInternals, interpretIR, hfind]
      split
      · exact hfnEq
      · rfl

/-- The legacy `_closed` goal is a corollary of the disjoint version: any
contract satisfying `LegacyCompatibleRuntimeContract` also satisfies
`DisjointRuntimeContract`. -/
theorem interpretIRWithInternalsZeroConservativeExtensionGoal_of_disjoint
    (contract : IRContract) :
    InterpretIRWithInternalsZeroConservativeExtensionGoalOfDisjoint contract →
      InterpretIRWithInternalsZeroConservativeExtensionGoal contract := by
  intro hdisjoint hlegacy tx initialState
  exact hdisjoint
    (disjointRuntimeContract_of_legacyCompatibleRuntimeContract contract hlegacy)
    tx initialState

/-! ## Positive helper-call characterization

The conservative extension chain above covers the case where function bodies are
disjoint from the internal table.  The following theorems characterize what happens
when a call **does** hit an internal helper: they give explicit unfolding equalities
for `evalIRCallWithInternals` and `execIRStmtWithInternals` on internal-function
call forms.  These are the IR-side building blocks that downstream compilation-model
proofs (for `Stmt.internalCallAssign` and `Expr.internalCall`) will consume. -/

/-- When argument evaluation succeeds and the callee is found in the internal table,
`evalIRCallWithInternals` delegates to `execIRInternalFunctionWithInternals`
(consuming one unit of fuel for the call itself). -/
theorem evalIRCallWithInternals_of_internal_function
    (contract : IRContract) (fuel : Nat) (state : IRState)
    (func : String) (args : List YulExpr)
    (helper : IRInternalFunctionDef) (argVals : List Nat) (state' : IRState)
    (hargs : evalIRExprsWithInternals contract (fuel + 1) state args = .values argVals state')
    (hfind : findInternalFunction? contract func = some helper) :
    evalIRCallWithInternals contract (fuel + 1) state func args =
      execIRInternalFunctionWithInternals contract fuel state' helper argVals := by
  simp only [evalIRCallWithInternals, hargs, hfind]

/-- When argument evaluation succeeds and no internal function is found,
`evalIRCallWithInternals` falls through to the builtin evaluation path. -/
theorem evalIRCallWithInternals_of_builtin
    (contract : IRContract) (fuel : Nat) (state : IRState)
    (func : String) (args : List YulExpr)
    (argVals : List Nat) (state' : IRState)
    (hargs : evalIRExprsWithInternals contract fuel state args = .values argVals state')
    (hfind : findInternalFunction? contract func = none) :
    evalIRCallWithInternals contract fuel state func args =
      match Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext
          Compiler.Proofs.YulGeneration.defaultBuiltinBackend
          state'.storage state'.sender state'.msgValue state'.thisAddress
          state'.blockTimestamp state'.blockNumber state'.chainId state'.blobBaseFee
          state'.selector state'.calldata func argVals with
      | some value => .values [value] state'
      | none => .revert state' := by
  simp only [evalIRCallWithInternals, hargs, hfind]

/-- When argument evaluation propagates a control-flow effect (stop/return/revert),
`evalIRCallWithInternals` propagates it unchanged. -/
theorem evalIRCallWithInternals_of_args_stop
    (contract : IRContract) (fuel : Nat) (state : IRState)
    (func : String) (args : List YulExpr) (state' : IRState)
    (hargs : evalIRExprsWithInternals contract fuel state args = .stop state') :
    evalIRCallWithInternals contract fuel state func args = .stop state' := by
  simp only [evalIRCallWithInternals, hargs]

theorem evalIRCallWithInternals_of_args_return
    (contract : IRContract) (fuel : Nat) (state : IRState)
    (func : String) (args : List YulExpr) (value : Nat) (state' : IRState)
    (hargs : evalIRExprsWithInternals contract fuel state args = .return value state') :
    evalIRCallWithInternals contract fuel state func args = .return value state' := by
  simp only [evalIRCallWithInternals, hargs]

theorem evalIRCallWithInternals_of_args_revert
    (contract : IRContract) (fuel : Nat) (state : IRState)
    (func : String) (args : List YulExpr) (state' : IRState)
    (hargs : evalIRExprsWithInternals contract fuel state args = .revert state') :
    evalIRCallWithInternals contract fuel state func args = .revert state' := by
  simp only [evalIRCallWithInternals, hargs]

/-- `execIRStmtWithInternals` for `.letMany names (.call func args)` unfolds
to `evalIRCallWithInternals` followed by a length-check and variable binding.
This is the IR execution path for compiled `Stmt.internalCallAssign`. -/
theorem execIRStmtWithInternals_letMany_call
    (contract : IRContract) (fuel : Nat) (state : IRState)
    (names : List String) (func : String) (args : List YulExpr) :
    execIRStmtWithInternals contract (fuel + 1) state (.letMany names (.call func args)) =
      match evalIRCallWithInternals contract fuel state func args with
      | .values values state' =>
          if names.length = values.length then
            .continue (state'.setVars (names.zip values))
          else
            .revert state'
      | .stop state' => .stop state'
      | .return value' state' => .return value' state'
      | .revert state' => .revert state' := by
  simp only [execIRStmtWithInternals]

/-- `evalIRExprWithInternals` for `.call func args` unfolds to a pattern match
on `evalIRCallWithInternals`: a single-valued result becomes a value, while
wrong-count results revert. -/
theorem evalIRExprWithInternals_call
    (contract : IRContract) (fuel : Nat) (state : IRState)
    (func : String) (args : List YulExpr) :
    evalIRExprWithInternals contract fuel state (.call func args) =
      match evalIRCallWithInternals contract fuel state func args with
      | .values [value] state' => .value value state'
      | .values _ state' => .revert state'
      | .stop state' => .stop state'
      | .return value state' => .return value state'
      | .revert state' => .revert state' := by
  simp only [evalIRExprWithInternals]

/-- Combined characterization for `Stmt.internalCallAssign` at the IR level:
when `.letMany names (.call func args)` executes with args evaluating to
`argVals` and `func` resolving to an internal helper, the result is determined
by `execIRInternalFunctionWithInternals`.  This chains
`execIRStmtWithInternals_letMany_call` + `evalIRCallWithInternals_of_internal_function`. -/
theorem execIRStmtWithInternals_letMany_call_internal
    (contract : IRContract) (fuel : Nat) (state : IRState)
    (names : List String) (func : String) (args : List YulExpr)
    (helper : IRInternalFunctionDef) (argVals : List Nat) (state' : IRState)
    (hargs : evalIRExprsWithInternals contract (fuel + 1) state args = .values argVals state')
    (hfind : findInternalFunction? contract func = some helper) :
    execIRStmtWithInternals contract (fuel + 2) state (.letMany names (.call func args)) =
      match execIRInternalFunctionWithInternals contract fuel state' helper argVals with
      | .values values state'' =>
          if names.length = values.length then
            .continue (state''.setVars (names.zip values))
          else
            .revert state''
      | .stop state'' => .stop state''
      | .return value' state'' => .return value' state''
      | .revert state'' => .revert state'' := by
  rw [show fuel + 2 = (fuel + 1) + 1 from by omega]
  rw [execIRStmtWithInternals_letMany_call]
  rw [evalIRCallWithInternals_of_internal_function contract fuel state func args helper argVals
    state' hargs hfind]

/-! ## Internal function execution characterization

Unfolding and decomposition theorems for `execIRInternalFunctionWithInternals`.
These are needed because the function is defined via well-founded recursion in the
mutual block and cannot be trivially `rfl`-unfolded. -/

/-- When fuel > 0 and params match, `execIRInternalFunctionWithInternals` prepares
the callee state, executes the body, and extracts return values or propagates
control flow. -/
theorem execIRInternalFunctionWithInternals_succ_of_params_match
    (contract : IRContract) (fuel : Nat) (callerState : IRState)
    (helper : IRInternalFunctionDef) (args : List Nat)
    (hlen : helper.params.length = args.length) :
    execIRInternalFunctionWithInternals contract (fuel + 1) callerState helper args =
      let calleeState := prepareInternalCalleeState callerState helper args
      match execIRStmtsWithInternals contract fuel calleeState helper.body with
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
          .revert callerState := by
  simp only [execIRInternalFunctionWithInternals, if_pos hlen]

/-- When fuel > 0 but params don't match, `execIRInternalFunctionWithInternals`
reverts with the caller state. -/
theorem execIRInternalFunctionWithInternals_succ_of_params_mismatch
    (contract : IRContract) (fuel : Nat) (callerState : IRState)
    (helper : IRInternalFunctionDef) (args : List Nat)
    (hlen : helper.params.length ≠ args.length) :
    execIRInternalFunctionWithInternals contract (fuel + 1) callerState helper args =
      .revert callerState := by
  simp only [execIRInternalFunctionWithInternals, if_neg hlen]

/-- At fuel 0, `execIRInternalFunctionWithInternals` always reverts. -/
theorem execIRInternalFunctionWithInternals_zero
    (contract : IRContract) (callerState : IRState)
    (helper : IRInternalFunctionDef) (args : List Nat) :
    execIRInternalFunctionWithInternals contract 0 callerState helper args =
      .revert callerState := by
  simp only [execIRInternalFunctionWithInternals]

/-- `restoreCallerVars` preserves storage (world state). -/
@[simp] theorem restoreCallerVars_storage
    (callerState calleeState : IRState) :
    (restoreCallerVars callerState calleeState).storage =
      calleeState.storage := by
  simp [restoreCallerVars]

/-- `restoreCallerVars` restores the caller's variable frame. -/
@[simp] theorem restoreCallerVars_vars
    (callerState calleeState : IRState) :
    (restoreCallerVars callerState calleeState).vars =
      callerState.vars := by
  simp [restoreCallerVars]

@[simp] theorem restoreCallerVars_sender
    (callerState calleeState : IRState) :
    (restoreCallerVars callerState calleeState).sender =
      calleeState.sender := by
  simp [restoreCallerVars]

@[simp] theorem restoreCallerVars_msgValue
    (callerState calleeState : IRState) :
    (restoreCallerVars callerState calleeState).msgValue =
      calleeState.msgValue := by
  simp [restoreCallerVars]

@[simp] theorem restoreCallerVars_thisAddress
    (callerState calleeState : IRState) :
    (restoreCallerVars callerState calleeState).thisAddress =
      calleeState.thisAddress := by
  simp [restoreCallerVars]

@[simp] theorem restoreCallerVars_blockTimestamp
    (callerState calleeState : IRState) :
    (restoreCallerVars callerState calleeState).blockTimestamp =
      calleeState.blockTimestamp := by
  simp [restoreCallerVars]

@[simp] theorem restoreCallerVars_blockNumber
    (callerState calleeState : IRState) :
    (restoreCallerVars callerState calleeState).blockNumber =
      calleeState.blockNumber := by
  simp [restoreCallerVars]

@[simp] theorem restoreCallerVars_chainId
    (callerState calleeState : IRState) :
    (restoreCallerVars callerState calleeState).chainId =
      calleeState.chainId := by
  simp [restoreCallerVars]

@[simp] theorem restoreCallerVars_returnValue
    (callerState calleeState : IRState) :
    (restoreCallerVars callerState calleeState).returnValue =
      calleeState.returnValue := by
  simp [restoreCallerVars]

@[simp] theorem restoreCallerVars_events
    (callerState calleeState : IRState) :
    (restoreCallerVars callerState calleeState).events =
      calleeState.events := by
  simp [restoreCallerVars]

/-- `IRState.setVar` only modifies the `vars` field, preserving all other fields. -/
@[simp] theorem IRState.setVar_storage (s : IRState) (name : String) (value : Nat) :
    (s.setVar name value).storage = s.storage := rfl

@[simp] theorem IRState.setVar_sender (s : IRState) (name : String) (value : Nat) :
    (s.setVar name value).sender = s.sender := rfl

@[simp] theorem IRState.setVar_msgValue (s : IRState) (name : String) (value : Nat) :
    (s.setVar name value).msgValue = s.msgValue := rfl

@[simp] theorem IRState.setVar_thisAddress (s : IRState) (name : String) (value : Nat) :
    (s.setVar name value).thisAddress = s.thisAddress := rfl

@[simp] theorem IRState.setVar_blockTimestamp (s : IRState) (name : String) (value : Nat) :
    (s.setVar name value).blockTimestamp = s.blockTimestamp := rfl

@[simp] theorem IRState.setVar_blockNumber (s : IRState) (name : String) (value : Nat) :
    (s.setVar name value).blockNumber = s.blockNumber := rfl

@[simp] theorem IRState.setVar_chainId (s : IRState) (name : String) (value : Nat) :
    (s.setVar name value).chainId = s.chainId := rfl

@[simp] theorem IRState.setVar_returnValue (s : IRState) (name : String) (value : Nat) :
    (s.setVar name value).returnValue = s.returnValue := rfl

@[simp] theorem IRState.setVar_events (s : IRState) (name : String) (value : Nat) :
    (s.setVar name value).events = s.events := rfl

private theorem setVars_field_preservation {f : IRState → α}
    (hsetVar : ∀ s name value, f (s.setVar name value) = f s)
    (s : IRState) (bindings : List (String × Nat)) :
    f (s.setVars bindings) = f s := by
  induction bindings generalizing s with
  | nil => rfl
  | cons hd tl ih =>
    show f (IRState.setVars (s.setVar hd.1 hd.2) tl) = f s
    rw [ih, hsetVar]

@[simp] theorem IRState.setVars_storage (s : IRState) (bindings : List (String × Nat)) :
    (s.setVars bindings).storage = s.storage :=
  setVars_field_preservation (fun _ _ _ => rfl) s bindings

@[simp] theorem IRState.setVars_sender (s : IRState) (bindings : List (String × Nat)) :
    (s.setVars bindings).sender = s.sender :=
  setVars_field_preservation (fun _ _ _ => rfl) s bindings

@[simp] theorem IRState.setVars_msgValue (s : IRState) (bindings : List (String × Nat)) :
    (s.setVars bindings).msgValue = s.msgValue :=
  setVars_field_preservation (fun _ _ _ => rfl) s bindings

@[simp] theorem IRState.setVars_thisAddress (s : IRState) (bindings : List (String × Nat)) :
    (s.setVars bindings).thisAddress = s.thisAddress :=
  setVars_field_preservation (fun _ _ _ => rfl) s bindings

@[simp] theorem IRState.setVars_blockTimestamp (s : IRState) (bindings : List (String × Nat)) :
    (s.setVars bindings).blockTimestamp = s.blockTimestamp :=
  setVars_field_preservation (fun _ _ _ => rfl) s bindings

@[simp] theorem IRState.setVars_blockNumber (s : IRState) (bindings : List (String × Nat)) :
    (s.setVars bindings).blockNumber = s.blockNumber :=
  setVars_field_preservation (fun _ _ _ => rfl) s bindings

@[simp] theorem IRState.setVars_chainId (s : IRState) (bindings : List (String × Nat)) :
    (s.setVars bindings).chainId = s.chainId :=
  setVars_field_preservation (fun _ _ _ => rfl) s bindings

@[simp] theorem IRState.setVars_returnValue (s : IRState) (bindings : List (String × Nat)) :
    (s.setVars bindings).returnValue = s.returnValue :=
  setVars_field_preservation (fun _ _ _ => rfl) s bindings

@[simp] theorem IRState.setVars_events (s : IRState) (bindings : List (String × Nat)) :
    (s.setVars bindings).events = s.events :=
  setVars_field_preservation (fun _ _ _ => rfl) s bindings

/-- `prepareInternalCalleeState` preserves storage from the caller. -/
@[simp] theorem prepareInternalCalleeState_storage
    (callerState : IRState) (helper : IRInternalFunctionDef) (args : List Nat) :
    (prepareInternalCalleeState callerState helper args).storage =
      callerState.storage := by
  simp [prepareInternalCalleeState]

/-- `prepareInternalCalleeState` preserves sender from the caller. -/
@[simp] theorem prepareInternalCalleeState_sender
    (callerState : IRState) (helper : IRInternalFunctionDef) (args : List Nat) :
    (prepareInternalCalleeState callerState helper args).sender =
      callerState.sender := by
  simp [prepareInternalCalleeState]

/-- `prepareInternalCalleeState` preserves msgValue from the caller. -/
@[simp] theorem prepareInternalCalleeState_msgValue
    (callerState : IRState) (helper : IRInternalFunctionDef) (args : List Nat) :
    (prepareInternalCalleeState callerState helper args).msgValue =
      callerState.msgValue := by
  simp [prepareInternalCalleeState]

/-- `prepareInternalCalleeState` preserves thisAddress from the caller. -/
@[simp] theorem prepareInternalCalleeState_thisAddress
    (callerState : IRState) (helper : IRInternalFunctionDef) (args : List Nat) :
    (prepareInternalCalleeState callerState helper args).thisAddress =
      callerState.thisAddress := by
  simp [prepareInternalCalleeState]

/-- `prepareInternalCalleeState` preserves blockTimestamp from the caller. -/
@[simp] theorem prepareInternalCalleeState_blockTimestamp
    (callerState : IRState) (helper : IRInternalFunctionDef) (args : List Nat) :
    (prepareInternalCalleeState callerState helper args).blockTimestamp =
      callerState.blockTimestamp := by
  simp [prepareInternalCalleeState]

/-- `prepareInternalCalleeState` preserves blockNumber from the caller. -/
@[simp] theorem prepareInternalCalleeState_blockNumber
    (callerState : IRState) (helper : IRInternalFunctionDef) (args : List Nat) :
    (prepareInternalCalleeState callerState helper args).blockNumber =
      callerState.blockNumber := by
  simp [prepareInternalCalleeState]

/-- `prepareInternalCalleeState` preserves chainId from the caller. -/
@[simp] theorem prepareInternalCalleeState_chainId
    (callerState : IRState) (helper : IRInternalFunctionDef) (args : List Nat) :
    (prepareInternalCalleeState callerState helper args).chainId =
      callerState.chainId := by
  simp [prepareInternalCalleeState]

/-- `prepareInternalCalleeState` preserves events from the caller. -/
@[simp] theorem prepareInternalCalleeState_events
    (callerState : IRState) (helper : IRInternalFunctionDef) (args : List Nat) :
    (prepareInternalCalleeState callerState helper args).events =
      callerState.events := by
  simp [prepareInternalCalleeState]

/-! ## Internal function lookup bridge

These theorems connect `SupportedCompiledInternalHelperWitness.presentInRuntime`
(which provides `compiledStmt ∈ runtimeContract.internalFunctions`) with the
`findInternalFunction?` lookup used by the IR interpreter. -/

@[simp] theorem irInternalFunctionDefOfStmt?_funcDef
    (name : String) (params rets : List String) (body : List YulStmt) :
    irInternalFunctionDefOfStmt? (YulStmt.funcDef name params rets body) =
      some { name, params, rets, body } := rfl

/-- If a `funcDef` statement is in `contract.internalFunctions`, then
`findInternalFunction?` succeeds for that name. -/
theorem findInternalFunction?_isSome_of_funcDef_mem
    (contract : IRContract) (name : String) (params rets : List String)
    (body : List YulStmt)
    (hmem : YulStmt.funcDef name params rets body ∈ contract.internalFunctions) :
    (findInternalFunction? contract name).isSome := by
  unfold findInternalFunction?
  rw [List.find?_isSome]
  exact ⟨⟨name, params, rets, body⟩,
    List.mem_filterMap.mpr ⟨_, hmem, rfl⟩,
    by simp⟩

/-- The result of `findInternalFunction?` always satisfies the name predicate
and comes from a `funcDef` in `internalFunctions`. -/
theorem findInternalFunction?_spec
    (contract : IRContract) (name : String) (helper : IRInternalFunctionDef)
    (hfind : findInternalFunction? contract name = some helper) :
    helper.name = name ∧
    YulStmt.funcDef helper.name helper.params helper.rets helper.body ∈
      contract.internalFunctions := by
  unfold findInternalFunction? at hfind
  constructor
  · have := List.find?_some hfind
    simp at this
    exact this
  · have hmem := List.mem_of_find?_eq_some hfind
    rw [List.mem_filterMap] at hmem
    obtain ⟨stmt, hstmt_mem, hstmt_def⟩ := hmem
    cases stmt with
    | funcDef n p r b =>
      simp [irInternalFunctionDefOfStmt?] at hstmt_def
      subst hstmt_def
      exact hstmt_mem
    | _ => simp [irInternalFunctionDefOfStmt?] at hstmt_def

/-- Under a uniqueness assumption on helper names, if a `funcDef` is in
`internalFunctions`, then `findInternalFunction?` returns a definition
with matching params, rets, and body. -/
theorem findInternalFunction?_exact_of_funcDef_mem_unique
    (contract : IRContract) (name : String) (params rets : List String)
    (body : List YulStmt)
    (hmem : YulStmt.funcDef name params rets body ∈ contract.internalFunctions)
    (hunique : ∀ stmt ∈ contract.internalFunctions,
      ∀ p r b, irInternalFunctionDefOfStmt? stmt = some ⟨name, p, r, b⟩ →
        p = params ∧ r = rets ∧ b = body) :
    findInternalFunction? contract name =
      some { name, params, rets, body } := by
  have hisSome := findInternalFunction?_isSome_of_funcDef_mem contract name params rets body hmem
  obtain ⟨helper, hhel⟩ := Option.isSome_iff_exists.mp hisSome
  have ⟨hname, hstmt_mem⟩ := findInternalFunction?_spec contract name helper hhel
  rw [hname] at hstmt_mem
  have hir : irInternalFunctionDefOfStmt?
      (YulStmt.funcDef name helper.params helper.rets helper.body) =
      some ⟨name, helper.params, helper.rets, helper.body⟩ := rfl
  obtain ⟨hp, hr, hb⟩ := hunique _ hstmt_mem _ _ _ hir
  have heq : helper = { name, params, rets, body } := by
    cases helper with | mk hn hp' hr' hb' =>
      simp only [IRInternalFunctionDef.mk.injEq] at hname hp hr hb ⊢
      exact ⟨hname, hp, hr, hb⟩
  rw [heq] at hhel
  exact hhel

/-! ## Singleton list characterization

The `CompiledStmtStepWithHelpersAndHelperIR.preserves` interface uses
`execIRStmtsWithInternals` (the list version).  When a statement compiles to a
singleton IR list, we can relate the list execution directly to the single
statement execution. -/

/-- On a singleton list with enough fuel, `execIRStmtsWithInternals` reduces to
`execIRStmtWithInternals` on the single element.  The `.continue` case stays
`.continue` because the empty-tail evaluation is trivially `.continue`. -/
theorem execIRStmtsWithInternals_singleton
    (contract : IRContract) (fuel : Nat) (state : IRState) (stmt : YulStmt) :
    execIRStmtsWithInternals contract (fuel + 1) state [stmt] =
      execIRStmtWithInternals contract fuel state stmt := by
  simp only [execIRStmtsWithInternals]
  cases execIRStmtWithInternals contract fuel state stmt with
  | «continue» state' => rfl
  | «return» value state' => rfl
  | stop state' => rfl
  | revert state' => rfl
  | «leave» state' => rfl

/-- End-to-end singleton list characterization for `Stmt.internalCallAssign`:
when `compiledIR = [.letMany names (.call func args)]` with args evaluating to
`argVals` and `func` resolving to an internal helper, the list execution result
is determined by `execIRInternalFunctionWithInternals`.  This is the IR-side
half of the `CompiledStmtStepWithHelpersAndHelperIR.preserves` goal for
`Stmt.internalCallAssign`. -/
theorem execIRStmtsWithInternals_singleton_letMany_call_internal
    (contract : IRContract) (fuel : Nat) (state : IRState)
    (names : List String) (func : String) (args : List YulExpr)
    (helper : IRInternalFunctionDef) (argVals : List Nat) (state' : IRState)
    (hargs : evalIRExprsWithInternals contract (fuel + 1) state args = .values argVals state')
    (hfind : findInternalFunction? contract func = some helper) :
    execIRStmtsWithInternals contract (fuel + 3) state
      [YulStmt.letMany names (YulExpr.call func args)] =
      match execIRInternalFunctionWithInternals contract fuel state' helper argVals with
      | .values values state'' =>
          if names.length = values.length then
            .continue (state''.setVars (names.zip values))
          else .revert state''
      | .stop state'' => .stop state''
      | .return value' state'' => .return value' state''
      | .revert state'' => .revert state'' := by
  rw [show fuel + 3 = (fuel + 2) + 1 from by omega]
  rw [execIRStmtsWithInternals_singleton]
  exact execIRStmtWithInternals_letMany_call_internal
    contract fuel state names func args helper argVals state' hargs hfind

@[simp] theorem applyIRTransactionContext_sender
    (tx : IRTransaction) (initialState : IRState) :
    (applyIRTransactionContext tx initialState).sender = tx.sender := by
  simp [applyIRTransactionContext]

@[simp] theorem applyIRTransactionContext_calldata
    (tx : IRTransaction) (initialState : IRState) :
    (applyIRTransactionContext tx initialState).calldata = tx.args := by
  simp [applyIRTransactionContext]

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
