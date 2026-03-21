import Compiler.CompilationModel.ExpressionCompile
import Compiler.Proofs.IRGeneration.ParamLoading
import Compiler.Proofs.IRGeneration.SourceSemantics
import Compiler.Proofs.IRGeneration.SupportedSpec
import Compiler.Proofs.IRGeneration.ExprCore

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

namespace FunctionBody

def lookupBinding? (bindings : List (String × Nat)) (name : String) : Option Nat :=
  bindings.find? (fun entry => entry.1 == name) |>.map Prod.snd

-- exprBoundNames, exprListBoundNames are now in ExprCore.lean

def exprBoundNamesPresent (expr : Expr) (bindings : List (String × Nat)) : Prop :=
  ∀ name, name ∈ exprBoundNames expr → ∃ value, lookupBinding? bindings name = some value

theorem lookupValue_eq_of_lookupBinding?_some
    {bindings : List (String × Nat)}
    {name : String}
    {value : Nat}
    (hlookup : lookupBinding? bindings name = some value) :
    SourceSemantics.lookupValue bindings name = value := by
  unfold lookupBinding? at hlookup
  unfold SourceSemantics.lookupValue
  simp [hlookup]

def bindingsExactlyMatchIRVars
    (bindings : List (String × Nat))
    (state : IRState) : Prop :=
  ∀ name, state.getVar name = lookupBinding? bindings name

def bindingsExactlyMatchIRVarsOnScope
    (scope : List String)
    (bindings : List (String × Nat))
    (state : IRState) : Prop :=
  ∀ name, name ∈ scope → state.getVar name = lookupBinding? bindings name

def bindingsExactlyMatchIRVarsOnExpr
    (expr : Expr)
    (bindings : List (String × Nat))
    (state : IRState) : Prop :=
  ∀ name, name ∈ exprBoundNames expr → state.getVar name = lookupBinding? bindings name

def bindingsMatchIRVars
    (bindings : List (String × Nat))
    (state : IRState) : Prop :=
  ∀ name, (state.getVar name).getD 0 = SourceSemantics.lookupValue bindings name

def bindingsBounded (bindings : List (String × Nat)) : Prop :=
  ∀ name, SourceSemantics.lookupValue bindings name < Compiler.Constants.evmModulus

theorem bindingsExactlyMatchIRVars_implies_bindingsMatchIRVars
    {bindings : List (String × Nat)}
    {state : IRState}
    (hexact : bindingsExactlyMatchIRVars bindings state) :
    bindingsMatchIRVars bindings state := by
  intro name
  rw [hexact name]
  rfl

theorem bindingsExactlyMatchIRVars_implies_onScope
    {scope : List String}
    {bindings : List (String × Nat)}
    {state : IRState}
    (hexact : bindingsExactlyMatchIRVars bindings state) :
    bindingsExactlyMatchIRVarsOnScope scope bindings state := by
  intro name _
  exact hexact name

theorem bindingsExactlyMatchIRVars_implies_onExpr
    {expr : Expr}
    {bindings : List (String × Nat)}
    {state : IRState}
    (hexact : bindingsExactlyMatchIRVars bindings state) :
    bindingsExactlyMatchIRVarsOnExpr expr bindings state := by
  intro name _
  exact hexact name

theorem bindingsExactlyMatchIRVarsOnExpr_of_subset
    {expr subexpr : Expr}
    {bindings : List (String × Nat)}
    {state : IRState}
    (hexact : bindingsExactlyMatchIRVarsOnExpr expr bindings state)
    (hsubset : ∀ name, name ∈ exprBoundNames subexpr → name ∈ exprBoundNames expr) :
    bindingsExactlyMatchIRVarsOnExpr subexpr bindings state := by
  intro name hname
  exact hexact name (hsubset name hname)


def runtimeStateMatchesIR
    (fields : List Field)
    (runtime : SourceSemantics.RuntimeState)
    (state : IRState) : Prop :=
  state.storage = SourceSemantics.encodeStorageAt fields runtime.world ∧
  state.transientStorage = (fun slot => (runtime.world.transientStorage slot).val) ∧
  state.sender = runtime.world.sender.val ∧
  state.msgValue = runtime.world.msgValue.val ∧
  state.thisAddress = runtime.world.thisAddress.val ∧
  state.blockTimestamp = runtime.world.blockTimestamp.val ∧
  state.blockNumber = runtime.world.blockNumber.val ∧
  state.chainId = runtime.world.chainId.val ∧
  state.returnValue = none ∧
  state.events = SourceSemantics.encodeEvents runtime.world.events

def initialIRStateForTx
    (spec : CompilationModel)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) : IRState :=
  { vars := []
    storage := SourceSemantics.encodeStorage spec initialWorld
    transientStorage := fun slot => (initialWorld.transientStorage slot).val
    memory := fun _ => 0
    calldata := tx.args
    returnValue := none
    sender := tx.sender
    msgValue := tx.msgValue
    thisAddress := tx.thisAddress
    blockTimestamp := tx.blockTimestamp
    blockNumber := tx.blockNumber
    chainId := tx.chainId
    blobBaseFee := tx.blobBaseFee
    selector := tx.functionSelector
    events := SourceSemantics.encodeEvents initialWorld.events }

@[simp] theorem bindingsMatchIRVars_nil_initialIRStateForTx
    (spec : CompilationModel)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) :
    bindingsMatchIRVars []
      (initialIRStateForTx spec tx initialWorld) := by
  intro name
  simp [initialIRStateForTx, IRState.getVar, SourceSemantics.lookupValue]

@[simp] theorem bindingsExactlyMatchIRVars_nil_initialIRStateForTx
    (spec : CompilationModel)
    (tx : IRTransaction)
  (initialWorld : Verity.ContractState) :
    bindingsExactlyMatchIRVars []
      (initialIRStateForTx spec tx initialWorld) := by
  intro name
  simp [lookupBinding?, initialIRStateForTx, IRState.getVar]

theorem evalIRExpr_ident_of_exact_bindings
    {bindings : List (String × Nat)}
    {state : IRState}
    (hexact : bindingsExactlyMatchIRVars bindings state)
    (name : String) :
    evalIRExpr state (YulExpr.ident name) = lookupBinding? bindings name := by
  simpa [evalIRExpr] using hexact name

theorem evalIRExpr_ident_of_scope_bindings
    {scope : List String}
    {bindings : List (String × Nat)}
    {state : IRState}
    (hexact : bindingsExactlyMatchIRVarsOnScope scope bindings state)
    {name : String}
    (hname : name ∈ scope) :
    evalIRExpr state (YulExpr.ident name) = lookupBinding? bindings name := by
  simpa [evalIRExpr] using hexact name hname

theorem evalIRExpr_caller_of_runtimeStateMatchesIR
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (YulExpr.call "caller" []) =
      some (SourceSemantics.evalExpr fields runtime (.caller)) := by
  rcases hmatch with ⟨_, _, hsender, _, _, _, _, _, _, _⟩
  simp [evalIRExpr, evalIRCall, SourceSemantics.evalExpr, hsender]

theorem evalIRExpr_contractAddress_of_runtimeStateMatchesIR
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (YulExpr.call "address" []) =
      some (SourceSemantics.evalExpr fields runtime (.contractAddress)) := by
  rcases hmatch with ⟨_, _, _, _, hthisAddress, _, _, _, _, _⟩
  simp [evalIRExpr, evalIRCall, SourceSemantics.evalExpr, hthisAddress]

theorem evalIRExpr_msgValue_of_runtimeStateMatchesIR
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (YulExpr.call "callvalue" []) =
      some (SourceSemantics.evalExpr fields runtime (.msgValue)) := by
  rcases hmatch with ⟨_, _, _, hmsgValue, _, _, _, _, _, _⟩
  simp [evalIRExpr, evalIRCall, SourceSemantics.evalExpr, hmsgValue]

theorem evalIRExpr_blockTimestamp_of_runtimeStateMatchesIR
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (YulExpr.call "timestamp" []) =
      some (SourceSemantics.evalExpr fields runtime (.blockTimestamp)) := by
  rcases hmatch with ⟨_, _, _, _, _, hblockTimestamp, _, _, _, _⟩
  simp [evalIRExpr, evalIRCall, SourceSemantics.evalExpr, hblockTimestamp]

theorem evalIRExpr_blockNumber_of_runtimeStateMatchesIR
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (YulExpr.call "number" []) =
      some (SourceSemantics.evalExpr fields runtime (.blockNumber)) := by
  rcases hmatch with ⟨_, _, _, _, _, _, hblockNumber, _, _, _⟩
  simp [evalIRExpr, evalIRCall, SourceSemantics.evalExpr, hblockNumber]

theorem evalIRExpr_chainid_of_runtimeStateMatchesIR
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (YulExpr.call "chainid" []) =
      some (SourceSemantics.evalExpr fields runtime (.chainid)) := by
  rcases hmatch with ⟨_, _, _, _, _, _, _, hchainId, _, _⟩
  simp [evalIRExpr, evalIRCall, SourceSemantics.evalExpr, hchainId]

theorem eval_compileExpr_caller
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (CompilationModel.compileExpr fields .calldata .caller |>.toOption.getD (YulExpr.lit 0)) =
      some (SourceSemantics.evalExpr fields runtime (.caller)) := by
  simp [CompilationModel.compileExpr]
  exact evalIRExpr_caller_of_runtimeStateMatchesIR hmatch

theorem eval_compileExpr_contractAddress
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (CompilationModel.compileExpr fields .calldata .contractAddress |>.toOption.getD (YulExpr.lit 0)) =
      some (SourceSemantics.evalExpr fields runtime (.contractAddress)) := by
  simp [CompilationModel.compileExpr]
  exact evalIRExpr_contractAddress_of_runtimeStateMatchesIR hmatch

theorem eval_compileExpr_msgValue
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (CompilationModel.compileExpr fields .calldata .msgValue |>.toOption.getD (YulExpr.lit 0)) =
      some (SourceSemantics.evalExpr fields runtime (.msgValue)) := by
  simp [CompilationModel.compileExpr]
  exact evalIRExpr_msgValue_of_runtimeStateMatchesIR hmatch

theorem eval_compileExpr_blockTimestamp
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (CompilationModel.compileExpr fields .calldata .blockTimestamp |>.toOption.getD (YulExpr.lit 0)) =
      some (SourceSemantics.evalExpr fields runtime (.blockTimestamp)) := by
  simp [CompilationModel.compileExpr]
  exact evalIRExpr_blockTimestamp_of_runtimeStateMatchesIR hmatch

theorem eval_compileExpr_blockNumber
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (CompilationModel.compileExpr fields .calldata .blockNumber |>.toOption.getD (YulExpr.lit 0)) =
      some (SourceSemantics.evalExpr fields runtime (.blockNumber)) := by
  simp [CompilationModel.compileExpr]
  exact evalIRExpr_blockNumber_of_runtimeStateMatchesIR hmatch

theorem eval_compileExpr_chainid
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (CompilationModel.compileExpr fields .calldata .chainid |>.toOption.getD (YulExpr.lit 0)) =
      some (SourceSemantics.evalExpr fields runtime (.chainid)) := by
  simp [CompilationModel.compileExpr]
  exact evalIRExpr_chainid_of_runtimeStateMatchesIR hmatch

theorem eval_compileExpr_literal
    (fields : List Field)
    (runtime : SourceSemantics.RuntimeState)
    (state : IRState)
    (value : Nat) :
    evalIRExpr state (YulExpr.lit (value % CompilationModel.uint256Modulus)) =
      some (SourceSemantics.evalExpr fields runtime (.literal value)) := by
   simp [evalIRExpr]
   change value % CompilationModel.uint256Modulus =
     SourceSemantics.wordNormalize value
   rw [ParamLoading.wordNormalize_eq_mod]
   rfl

@[simp] theorem boolWord_eq_if (p : Prop) [Decidable p] :
    SourceSemantics.boolWord (decide p) = (if p then 1 else 0) := by
  by_cases hp : p <;> simp [SourceSemantics.boolWord, hp]

theorem evalIRExpr_iszero_of_lt
    {state : IRState}
    {expr : YulExpr}
    {value : Nat}
    (heval : evalIRExpr state expr = some value)
    (hvalueLt : value < Compiler.Constants.evmModulus) :
    evalIRExpr state (YulExpr.call "iszero" [expr]) =
      some (SourceSemantics.boolWord (value = 0)) := by
  by_cases hzero : value = 0
  · subst hzero
    simp [evalIRExpr, evalIRCall, evalIRExprs, heval,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext,
      SourceSemantics.boolWord]
  · have hmod : value % Compiler.Constants.evmModulus = value := Nat.mod_eq_of_lt hvalueLt
    simp [evalIRExpr, evalIRCall, evalIRExprs, heval, hmod, hzero,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext,
      SourceSemantics.boolWord]

theorem evalIRExpr_yulToBool_of_lt
    {state : IRState}
    {expr : YulExpr}
    {value : Nat}
    (heval : evalIRExpr state expr = some value)
    (hvalueLt : value < Compiler.Constants.evmModulus) :
    evalIRExpr state (CompilationModel.yulToBool expr) =
      some (SourceSemantics.boolWord (value ≠ 0)) := by
  by_cases hzero : value = 0
  · subst hzero
    simp [CompilationModel.yulToBool, evalIRExpr, evalIRCall, evalIRExprs, heval,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext,
      SourceSemantics.boolWord]
  · have hmod : value % Compiler.Constants.evmModulus = value := Nat.mod_eq_of_lt hvalueLt
    simp [CompilationModel.yulToBool, evalIRExpr, evalIRCall, evalIRExprs, heval, hmod, hzero,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext,
      SourceSemantics.boolWord]

theorem evalIRExpr_add_of_eval
    {state : IRState}
    {lhs rhs : YulExpr}
    {a b : Nat}
    (hlhs : evalIRExpr state lhs = some a)
    (hrhs : evalIRExpr state rhs = some b) :
    evalIRExpr state (YulExpr.call "add" [lhs, rhs]) =
      some ((a + b) % Compiler.Constants.evmModulus) := by
  simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext]

theorem evalIRExpr_sub_of_eval
    {state : IRState}
    {lhs rhs : YulExpr}
    {a b : Nat}
    (hlhs : evalIRExpr state lhs = some a)
    (hrhs : evalIRExpr state rhs = some b) :
    evalIRExpr state (YulExpr.call "sub" [lhs, rhs]) =
      some ((Compiler.Constants.evmModulus + (a % Compiler.Constants.evmModulus) -
        (b % Compiler.Constants.evmModulus)) % Compiler.Constants.evmModulus) := by
  simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext]

theorem evalIRExpr_mul_of_eval
    {state : IRState}
    {lhs rhs : YulExpr}
    {a b : Nat}
    (hlhs : evalIRExpr state lhs = some a)
    (hrhs : evalIRExpr state rhs = some b) :
    evalIRExpr state (YulExpr.call "mul" [lhs, rhs]) =
      some ((a * b) % Compiler.Constants.evmModulus) := by
  simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext]

theorem evalIRExpr_div_of_eval
    {state : IRState}
    {lhs rhs : YulExpr}
    {a b : Nat}
    (hlhs : evalIRExpr state lhs = some a)
    (hrhs : evalIRExpr state rhs = some b) :
    evalIRExpr state (YulExpr.call "div" [lhs, rhs]) =
      some (if b % Compiler.Constants.evmModulus = 0 then 0 else
        (a % Compiler.Constants.evmModulus) / (b % Compiler.Constants.evmModulus)) := by
  by_cases hzero : b % Compiler.Constants.evmModulus = 0
  · simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs, hzero,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext]
  · simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs, hzero,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext]

theorem evalIRExpr_mod_of_eval
    {state : IRState}
    {lhs rhs : YulExpr}
    {a b : Nat}
    (hlhs : evalIRExpr state lhs = some a)
    (hrhs : evalIRExpr state rhs = some b) :
    evalIRExpr state (YulExpr.call "mod" [lhs, rhs]) =
      some (if b % Compiler.Constants.evmModulus = 0 then 0 else
        (a % Compiler.Constants.evmModulus) % (b % Compiler.Constants.evmModulus)) := by
  by_cases hzero : b % Compiler.Constants.evmModulus = 0
  · simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs, hzero,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext]
  · simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs, hzero,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext]

theorem evalIRExpr_eq_of_eval
    {state : IRState}
    {lhs rhs : YulExpr}
    {a b : Nat}
    (hlhs : evalIRExpr state lhs = some a)
    (hrhs : evalIRExpr state rhs = some b) :
    evalIRExpr state (YulExpr.call "eq" [lhs, rhs]) =
      some (SourceSemantics.boolWord (a % Compiler.Constants.evmModulus =
        b % Compiler.Constants.evmModulus)) := by
  by_cases heq : a % Compiler.Constants.evmModulus = b % Compiler.Constants.evmModulus
  · simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs, heq,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext,
      SourceSemantics.boolWord]
  · simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs, heq,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext,
      SourceSemantics.boolWord]

theorem evalIRExpr_lt_of_eval
    {state : IRState}
    {lhs rhs : YulExpr}
    {a b : Nat}
    (hlhs : evalIRExpr state lhs = some a)
    (hrhs : evalIRExpr state rhs = some b) :
    evalIRExpr state (YulExpr.call "lt" [lhs, rhs]) =
      some (SourceSemantics.boolWord (a % Compiler.Constants.evmModulus <
        b % Compiler.Constants.evmModulus)) := by
  by_cases hlt : a % Compiler.Constants.evmModulus < b % Compiler.Constants.evmModulus
  · simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs, hlt,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext,
      SourceSemantics.boolWord]
  · simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs, hlt,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext,
      SourceSemantics.boolWord]

theorem evalIRExpr_gt_of_eval
    {state : IRState}
    {lhs rhs : YulExpr}
    {a b : Nat}
    (hlhs : evalIRExpr state lhs = some a)
    (hrhs : evalIRExpr state rhs = some b) :
    evalIRExpr state (YulExpr.call "gt" [lhs, rhs]) =
      some (SourceSemantics.boolWord (b % Compiler.Constants.evmModulus <
        a % Compiler.Constants.evmModulus)) := by
  by_cases hgt : b % Compiler.Constants.evmModulus < a % Compiler.Constants.evmModulus
  · have hcmp : ¬ a % Compiler.Constants.evmModulus ≤ b % Compiler.Constants.evmModulus := by
      exact Nat.not_le_of_gt hgt
    simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs, hgt,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext,
      SourceSemantics.boolWord]
  · have hcmp : a % Compiler.Constants.evmModulus ≤ b % Compiler.Constants.evmModulus := by
      exact Nat.le_of_not_gt hgt
    simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs, hgt,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext,
      SourceSemantics.boolWord]

theorem evalIRExpr_and_of_eval
    {state : IRState}
    {lhs rhs : YulExpr}
    {a b : Nat}
    (hlhs : evalIRExpr state lhs = some a)
    (hrhs : evalIRExpr state rhs = some b) :
    evalIRExpr state (YulExpr.call "and" [lhs, rhs]) =
      some ((a % Compiler.Constants.evmModulus) &&& (b % Compiler.Constants.evmModulus)) := by
  simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext]

theorem evalIRExpr_or_of_eval
    {state : IRState}
    {lhs rhs : YulExpr}
    {a b : Nat}
    (hlhs : evalIRExpr state lhs = some a)
    (hrhs : evalIRExpr state rhs = some b) :
    evalIRExpr state (YulExpr.call "or" [lhs, rhs]) =
      some ((a % Compiler.Constants.evmModulus) ||| (b % Compiler.Constants.evmModulus)) := by
  simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext]

theorem evalIRExpr_xor_of_eval
    {state : IRState}
    {lhs rhs : YulExpr}
    {a b : Nat}
    (hlhs : evalIRExpr state lhs = some a)
    (hrhs : evalIRExpr state rhs = some b) :
    evalIRExpr state (YulExpr.call "xor" [lhs, rhs]) =
      some (Nat.xor (a % Compiler.Constants.evmModulus) (b % Compiler.Constants.evmModulus)) := by
  simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext]

theorem evalIRExpr_not_of_eval
    {state : IRState}
    {expr : YulExpr}
    {value : Nat}
    (heval : evalIRExpr state expr = some value) :
    evalIRExpr state (YulExpr.call "not" [expr]) =
      some (Nat.xor (value % Compiler.Constants.evmModulus)
        (Compiler.Constants.evmModulus - 1)) := by
  simp [evalIRExpr, evalIRCall, evalIRExprs, heval,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext]

theorem evalIRExpr_shl_of_eval
    {state : IRState}
    {shiftExpr valueExpr : YulExpr}
    {shift value : Nat}
    (hshift : evalIRExpr state shiftExpr = some shift)
    (hvalue : evalIRExpr state valueExpr = some value) :
    evalIRExpr state (YulExpr.call "shl" [shiftExpr, valueExpr]) =
      some (if shift % Compiler.Constants.evmModulus < 256 then
        ((value % Compiler.Constants.evmModulus) *
          2 ^ (shift % Compiler.Constants.evmModulus)) % Compiler.Constants.evmModulus
      else
        0) := by
  by_cases hlt : shift % Compiler.Constants.evmModulus < 256
  · simp [evalIRExpr, evalIRCall, evalIRExprs, hshift, hvalue, hlt,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext]
  · simp [evalIRExpr, evalIRCall, evalIRExprs, hshift, hvalue, hlt,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext]

theorem evalIRExpr_shr_of_eval
    {state : IRState}
    {shiftExpr valueExpr : YulExpr}
    {shift value : Nat}
    (hshift : evalIRExpr state shiftExpr = some shift)
    (hvalue : evalIRExpr state valueExpr = some value) :
    evalIRExpr state (YulExpr.call "shr" [shiftExpr, valueExpr]) =
      some (if shift % Compiler.Constants.evmModulus < 256 then
        (value % Compiler.Constants.evmModulus) /
          2 ^ (shift % Compiler.Constants.evmModulus)
      else
        0) := by
  by_cases hlt : shift % Compiler.Constants.evmModulus < 256
  · simp [evalIRExpr, evalIRCall, evalIRExprs, hshift, hvalue, hlt,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext]
  · simp [evalIRExpr, evalIRCall, evalIRExprs, hshift, hvalue, hlt,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext]

private theorem findEntry_filter_ne_eq_findEntry
    (entries : List (String × Nat))
    (blockedName queryName : String)
    (hNe : queryName ≠ blockedName) :
    List.find? (fun entry => entry.1 == queryName)
        (entries.filter (fun entry => entry.1 != blockedName)) =
      List.find? (fun entry => entry.1 == queryName) entries := by
  induction entries with
  | nil =>
      simp
  | cons entry rest ih =>
      by_cases hBlocked : entry.1 = blockedName
      · subst hBlocked
        have hHeadNe : entry.1 ≠ queryName := by
          intro hHeadEq
          apply hNe
          simp [hHeadEq]
        simp [hHeadNe, ih]
      · by_cases hQuery : entry.1 = queryName
        · subst hQuery
          simp [hBlocked]
        · simp [hBlocked, hQuery, ih]

@[simp] theorem getVar_setVar_eq
    (state : IRState)
    (name : String)
    (value : Nat) :
    (state.setVar name value).getVar name = some value := by
  simp [IRState.getVar, IRState.setVar]

theorem getVar_setVar_ne
    (state : IRState)
    (boundName queryName : String)
    (value : Nat)
    (hNe : queryName ≠ boundName) :
    (state.setVar boundName value).getVar queryName = state.getVar queryName := by
  have hNe' : boundName ≠ queryName := by
    intro hEq
    apply hNe
    simp [hEq]
  calc
    (state.setVar boundName value).getVar queryName
        =
          Option.map Prod.snd
            (List.find? (fun entry => entry.1 == queryName)
              ((boundName, value) :: List.filter (fun entry => entry.1 != boundName) state.vars)) := by
                rfl
    _ = Option.map Prod.snd
          (List.find? (fun entry => entry.1 == queryName)
            (List.filter (fun entry => entry.1 != boundName) state.vars)) := by
              simp [hNe']
    _ = Option.map Prod.snd
          (List.find? (fun entry => entry.1 == queryName) state.vars) := by
              rw [findEntry_filter_ne_eq_findEntry state.vars boundName queryName hNe]
    _ = state.getVar queryName := by
          rfl

@[simp] theorem lookupValue_bindValue_eq
    (bindings : List (String × Nat))
    (name : String)
    (value : Nat) :
    SourceSemantics.lookupValue
      (SourceSemantics.bindValue bindings name value)
      name = value := by
  simp [SourceSemantics.lookupValue, SourceSemantics.bindValue]

theorem lookupValue_bindValue_ne
    (bindings : List (String × Nat))
    (boundName queryName : String)
    (value : Nat)
    (hNe : queryName ≠ boundName) :
    SourceSemantics.lookupValue
      (SourceSemantics.bindValue bindings boundName value)
      queryName =
    SourceSemantics.lookupValue bindings queryName := by
  have hNe' : boundName ≠ queryName := by
    intro hEq
    apply hNe
    simp [hEq]
  calc
    SourceSemantics.lookupValue
        (SourceSemantics.bindValue bindings boundName value)
        queryName
        =
          (Option.map Prod.snd
            (List.find? (fun entry => entry.1 == queryName)
              ((boundName, value) :: List.filter (fun entry => entry.1 != boundName) bindings))).getD 0 := by
                rfl
    _ = (Option.map Prod.snd
          (List.find? (fun entry => entry.1 == queryName)
            (List.filter (fun entry => entry.1 != boundName) bindings))).getD 0 := by
              simp [hNe']
    _ = (Option.map Prod.snd
          (List.find? (fun entry => entry.1 == queryName) bindings)).getD 0 := by
              rw [findEntry_filter_ne_eq_findEntry bindings boundName queryName hNe]
    _ = SourceSemantics.lookupValue bindings queryName := by
          rfl

@[simp] theorem bindingsBounded_nil :
    bindingsBounded [] := by
  intro name
  simp [SourceSemantics.lookupValue, Compiler.Constants.evmModulus]

@[simp] theorem wordNormalize_lt_evmModulus (value : Nat) :
    SourceSemantics.wordNormalize value < Compiler.Constants.evmModulus := by
  rw [ParamLoading.wordNormalize_eq_mod]
  exact Nat.mod_lt _ (by simp [Compiler.Constants.evmModulus])

theorem decodeSupportedParamWord_lt_evmModulus
    {ty : ParamType}
    {word value : Nat}
    (hdecode : SourceSemantics.decodeSupportedParamWord ty word = some value) :
    value < Compiler.Constants.evmModulus := by
  cases ty <;> simp [SourceSemantics.decodeSupportedParamWord, SourceSemantics.uint8Modulus] at hdecode ⊢
  · subst value
    exact wordNormalize_lt_evmModulus word
  · subst value
    exact Nat.lt_of_le_of_lt Nat.and_le_left (wordNormalize_lt_evmModulus word)
  · subst value
    exact Nat.lt_of_le_of_lt Nat.and_le_left (wordNormalize_lt_evmModulus word)
  · split at hdecode
    · injection hdecode with hvalue
      subst hvalue
      simp [Compiler.Constants.evmModulus]
    · split at hdecode
      · injection hdecode with hvalue
        subst hvalue
        simp [Compiler.Constants.evmModulus]
      · contradiction
  · subst value
    exact wordNormalize_lt_evmModulus word

theorem bindingsBounded_bindValue
    {bindings : List (String × Nat)}
    (hbounded : bindingsBounded bindings)
    (boundName : String)
    (value : Nat)
    (hvalueLt : value < Compiler.Constants.evmModulus) :
    bindingsBounded (SourceSemantics.bindValue bindings boundName value) := by
  intro queryName
  by_cases hEq : queryName = boundName
  · subst hEq
    simp [lookupValue_bindValue_eq, hvalueLt]
  · rw [lookupValue_bindValue_ne bindings boundName queryName value hEq]
    exact hbounded queryName

private theorem bindingsBounded_cons
    {bindings : List (String × Nat)}
    (boundName : String)
    (value : Nat)
    (hvalueLt : value < Compiler.Constants.evmModulus)
    (hbounded : bindingsBounded bindings) :
    bindingsBounded ((boundName, value) :: bindings) := by
  intro queryName
  by_cases hEq : queryName = boundName
  · subst hEq
    simp [SourceSemantics.lookupValue, hvalueLt]
  · have hlookup :
        SourceSemantics.lookupValue ((boundName, value) :: bindings) queryName =
          SourceSemantics.lookupValue bindings queryName := by
        have hEq' : boundName ≠ queryName := by
          intro hEq'
          apply hEq
          exact hEq'.symm
        unfold SourceSemantics.lookupValue
        simp [hEq']
    rw [hlookup]
    exact hbounded queryName

theorem bindingsBounded_of_bindSupportedParams
    {params : List Param}
    {args : List Nat}
    {bindings : List (String × Nat)}
    (hbind : SourceSemantics.bindSupportedParams params args = some bindings) :
    bindingsBounded bindings := by
  induction params generalizing args bindings with
  | nil =>
      simp [SourceSemantics.bindSupportedParams] at hbind
      cases hbind
      simp
  | cons param rest ih =>
      cases args with
      | nil =>
          simp [SourceSemantics.bindSupportedParams] at hbind
      | cons arg restArgs =>
          cases hdecode : SourceSemantics.decodeSupportedParamWord param.ty arg <;>
              simp [SourceSemantics.bindSupportedParams, hdecode] at hbind
          case some value =>
            cases hrest : SourceSemantics.bindSupportedParams rest restArgs <;>
                simp [hrest] at hbind
            case some restBindings =>
              cases hbind
              exact bindingsBounded_cons
                param.name value (decodeSupportedParamWord_lt_evmModulus hdecode) (ih hrest)

@[simp] theorem lookupBinding?_bindValue_eq
    (bindings : List (String × Nat))
    (name : String)
    (value : Nat) :
    lookupBinding?
      (SourceSemantics.bindValue bindings name value)
      name = some value := by
  simp [lookupBinding?, SourceSemantics.bindValue]

theorem lookupBinding?_bindValue_ne
    (bindings : List (String × Nat))
    (boundName queryName : String)
    (value : Nat)
    (hNe : queryName ≠ boundName) :
    lookupBinding?
      (SourceSemantics.bindValue bindings boundName value)
      queryName =
    lookupBinding? bindings queryName := by
  have hNe' : boundName ≠ queryName := by
    intro hEq
    apply hNe
    simp [hEq]
  calc
    lookupBinding?
        (SourceSemantics.bindValue bindings boundName value)
        queryName
        =
          Option.map Prod.snd
            (List.find? (fun entry => entry.1 == queryName)
              ((boundName, value) :: List.filter (fun entry => entry.1 != boundName) bindings)) := by
                rfl
    _ = Option.map Prod.snd
          (List.find? (fun entry => entry.1 == queryName)
            (List.filter (fun entry => entry.1 != boundName) bindings)) := by
              simp [hNe']
    _ = Option.map Prod.snd
          (List.find? (fun entry => entry.1 == queryName) bindings) := by
              rw [findEntry_filter_ne_eq_findEntry bindings boundName queryName hNe]
    _ = lookupBinding? bindings queryName := by
          rfl

theorem exprBoundNamesPresent_bindValue
    (expr : Expr)
    (bindings : List (String × Nat))
    (boundName : String)
    (value : Nat)
    (hpresent : exprBoundNamesPresent expr bindings) :
    exprBoundNamesPresent expr (SourceSemantics.bindValue bindings boundName value) := by
  intro queryName hmem
  by_cases hEq : queryName = boundName
  · subst hEq
    exact ⟨value, lookupBinding?_bindValue_eq bindings queryName value⟩
  · rcases hpresent queryName hmem with ⟨found, hfound⟩
    exact ⟨found, by rw [lookupBinding?_bindValue_ne bindings boundName queryName value hEq, hfound]⟩

theorem bindSupportedParams_lookupBinding?_some_of_mem
    {params : List Param}
    {args : List Nat}
    {bindings : List (String × Nat)}
    (hparamsNodup : (params.map Param.name).Nodup)
    (hbind : SourceSemantics.bindSupportedParams params args = some bindings)
    {queryName : String}
    (hmem : queryName ∈ params.map Param.name) :
    ∃ value, lookupBinding? bindings queryName = some value := by
  induction params generalizing args bindings with
  | nil =>
      cases hmem
  | cons param rest ih =>
      cases args with
      | nil =>
          simp [SourceSemantics.bindSupportedParams] at hbind
      | cons arg restArgs =>
          have hrestNodup : (rest.map Param.name).Nodup := by
            exact (List.nodup_cons.mp hparamsNodup).2
          cases hdecode : SourceSemantics.decodeSupportedParamWord param.ty arg <;>
              simp [SourceSemantics.bindSupportedParams, hdecode] at hbind
          case some value =>
            cases hrest : SourceSemantics.bindSupportedParams rest restArgs <;>
                simp [hrest] at hbind
            case some restBindings =>
              cases hbind
              simp only [List.map, List.mem_cons] at hmem
              rcases hmem with rfl | hmemRest
              · exact ⟨value, by simp [lookupBinding?]⟩
              · have hqueryNe : queryName ≠ param.name := by
                  intro hEq
                  apply (List.nodup_cons.mp hparamsNodup).1
                  simpa [hEq] using hmemRest
                have hqueryNe' : ¬ param.name = queryName := by
                  intro hEq
                  apply hqueryNe
                  exact hEq.symm
                rcases ih hrestNodup hrest hmemRest with ⟨found, hfound⟩
                have hfindSome : ∃ entryName,
                    List.find? (fun entry => entry.1 == queryName) restBindings =
                      some (entryName, found) := by
                  unfold lookupBinding? at hfound
                  cases hfind : List.find? (fun entry => entry.1 == queryName) restBindings with
                  | none =>
                      simp [hfind] at hfound
                  | some entry =>
                      cases entry with
                      | mk entryName entryValue =>
                          simp [hfind] at hfound
                          cases hfound
                          exact ⟨entryName, rfl⟩
                rcases hfindSome with ⟨entryName, hfindSome⟩
                exact ⟨found, by
                  unfold lookupBinding?
                  simp [hqueryNe', hfindSome]⟩

theorem exprBoundNamesPresent_of_bindSupportedParams
    {expr : Expr}
    {params : List Param}
    {args : List Nat}
    {bindings : List (String × Nat)}
    (hparamsNodup : (params.map Param.name).Nodup)
    (hbind : SourceSemantics.bindSupportedParams params args = some bindings)
    (hsubset : ∀ name, name ∈ exprBoundNames expr → name ∈ params.map Param.name) :
    exprBoundNamesPresent expr bindings := by
  intro queryName hmem
  exact bindSupportedParams_lookupBinding?_some_of_mem hparamsNodup hbind (hsubset queryName hmem)

theorem bindingsExactlyMatchIRVars_setVar_bindValue
    {bindings : List (String × Nat)}
    {state : IRState}
    (hexact : bindingsExactlyMatchIRVars bindings state)
    (boundName : String)
    (value : Nat) :
    bindingsExactlyMatchIRVars
      (SourceSemantics.bindValue bindings boundName value)
      (state.setVar boundName value) := by
  intro queryName
  by_cases hEq : queryName = boundName
  · subst hEq
    simp [lookupBinding?_bindValue_eq]
  · rw [getVar_setVar_ne state boundName queryName value hEq,
      lookupBinding?_bindValue_ne bindings boundName queryName value hEq]
    exact hexact queryName

theorem bindingsMatchIRVars_setVar_bindValue
    {bindings : List (String × Nat)}
    {state : IRState}
    (hmatch : bindingsMatchIRVars bindings state)
    (boundName : String)
    (value : Nat) :
    bindingsMatchIRVars
      (SourceSemantics.bindValue bindings boundName value)
      (state.setVar boundName value) := by
  intro queryName
  by_cases hEq : queryName = boundName
  · subst hEq
    simp
  · rw [getVar_setVar_ne state boundName queryName value hEq,
      lookupValue_bindValue_ne bindings boundName queryName value hEq]
    exact hmatch queryName

theorem bindingsExactlyMatchIRVars_applyBindingsToIRState
    {bindings0 bindings : List (String × Nat)}
    {state : IRState}
    (hexact : bindingsExactlyMatchIRVars bindings0 state) :
    bindingsExactlyMatchIRVars
      (bindings.foldl (fun acc entry => SourceSemantics.bindValue acc entry.1 entry.2) bindings0)
      (ParamLoading.applyBindingsToIRState state bindings) := by
  induction bindings generalizing bindings0 state with
  | nil =>
      simpa [ParamLoading.applyBindingsToIRState]
  | cons entry rest ih =>
      have hstep :
          bindingsExactlyMatchIRVars
            (SourceSemantics.bindValue bindings0 entry.1 entry.2)
            (state.setVar entry.1 entry.2) :=
        bindingsExactlyMatchIRVars_setVar_bindValue hexact entry.1 entry.2
      simpa [ParamLoading.applyBindingsToIRState, List.foldl] using
        ih (bindings0 := SourceSemantics.bindValue bindings0 entry.1 entry.2)
          (state := state.setVar entry.1 entry.2) hstep

theorem evalIRExpr_sload_of_runtimeStateMatchesIR
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state)
    (slot : Nat) :
    evalIRExpr state (YulExpr.call "sload" [YulExpr.lit slot]) =
      some (SourceSemantics.encodeStorageAt fields runtime.world slot) := by
  rcases hmatch with ⟨hstorage, _, _, _, _, _, _, _, _⟩
  simp [evalIRExpr, evalIRCall, evalIRExprs,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext, hstorage]

theorem eval_compileExpr_param_of_exact_bindings
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (name : String)
    (hexact : bindingsExactlyMatchIRVars runtime.bindings state)
    (hpresent : exprBoundNamesPresent (.param name) runtime.bindings) :
    evalIRExpr state (YulExpr.ident name) =
      some (SourceSemantics.evalExpr fields runtime (.param name)) := by
   rcases hpresent name (by simp [exprBoundNames]) with ⟨value, hlookup⟩
   have hident := evalIRExpr_ident_of_exact_bindings hexact name
   rw [hlookup] at hident
   have hsource : SourceSemantics.evalExpr fields runtime (.param name) = value := by
     change SourceSemantics.lookupValue runtime.bindings name = value
     exact lookupValue_eq_of_lookupBinding?_some hlookup
   rw [hsource]
   exact hident

theorem eval_compileExpr_localVar_of_exact_bindings
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (name : String)
    (hexact : bindingsExactlyMatchIRVars runtime.bindings state)
    (hpresent : exprBoundNamesPresent (.localVar name) runtime.bindings) :
    evalIRExpr state (YulExpr.ident name) =
      some (SourceSemantics.evalExpr fields runtime (.localVar name)) := by
   rcases hpresent name (by simp [exprBoundNames]) with ⟨value, hlookup⟩
   have hident := evalIRExpr_ident_of_exact_bindings hexact name
   rw [hlookup] at hident
   have hsource : SourceSemantics.evalExpr fields runtime (.localVar name) = value := by
     change SourceSemantics.lookupValue runtime.bindings name = value
     exact lookupValue_eq_of_lookupBinding?_some hlookup
   rw [hsource]
   exact hident

theorem eval_compileExpr_param_of_expr_bindings
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (name : String)
    (hexact : bindingsExactlyMatchIRVarsOnExpr (.param name) runtime.bindings state)
    (hpresent : exprBoundNamesPresent (.param name) runtime.bindings) :
    evalIRExpr state (YulExpr.ident name) =
      some (SourceSemantics.evalExpr fields runtime (.param name)) := by
   rcases hpresent name (by simp [exprBoundNames]) with ⟨value, hlookup⟩
   have hident := hexact name (by simp [exprBoundNames])
   rw [hlookup] at hident
   have hsource : SourceSemantics.evalExpr fields runtime (.param name) = value := by
     change SourceSemantics.lookupValue runtime.bindings name = value
     exact lookupValue_eq_of_lookupBinding?_some hlookup
   rw [hsource]
   simpa [evalIRExpr] using hident

theorem eval_compileExpr_localVar_of_expr_bindings
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (name : String)
    (hexact : bindingsExactlyMatchIRVarsOnExpr (.localVar name) runtime.bindings state)
    (hpresent : exprBoundNamesPresent (.localVar name) runtime.bindings) :
    evalIRExpr state (YulExpr.ident name) =
      some (SourceSemantics.evalExpr fields runtime (.localVar name)) := by
   rcases hpresent name (by simp [exprBoundNames]) with ⟨value, hlookup⟩
   have hident := hexact name (by simp [exprBoundNames])
   rw [hlookup] at hident
   have hsource : SourceSemantics.evalExpr fields runtime (.localVar name) = value := by
     change SourceSemantics.lookupValue runtime.bindings name = value
     exact lookupValue_eq_of_lookupBinding?_some hlookup
   rw [hsource]
   simpa [evalIRExpr] using hident

@[simp] theorem boolWord_lt_evmModulus (b : Bool) :
    SourceSemantics.boolWord b < Compiler.Constants.evmModulus := by
  cases b <;> norm_num [SourceSemantics.boolWord, Compiler.Constants.evmModulus]

@[simp] theorem boolWord_and
    (a b : Bool) :
    (SourceSemantics.boolWord a &&& SourceSemantics.boolWord b) =
      SourceSemantics.boolWord (a && b) := by
  cases a <;> cases b <;>
    simp [SourceSemantics.boolWord]

@[simp] theorem boolWord_or
    (a b : Bool) :
    (SourceSemantics.boolWord a ||| SourceSemantics.boolWord b) =
      SourceSemantics.boolWord (a || b) := by
  cases a <;> cases b <;>
    simp [SourceSemantics.boolWord]

theorem compileExpr_eq_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.eq lhs rhs) =
      Except.ok (YulExpr.call "eq" [lhsIR, rhsIR]) := by
  rw [CompilationModel.compileExpr, hlhs, hrhs]
  rfl

theorem compileExpr_lt_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.lt lhs rhs) =
      Except.ok (YulExpr.call "lt" [lhsIR, rhsIR]) := by
  rw [CompilationModel.compileExpr, hlhs, hrhs]
  rfl

theorem compileExpr_gt_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.gt lhs rhs) =
      Except.ok (YulExpr.call "gt" [lhsIR, rhsIR]) := by
  rw [CompilationModel.compileExpr, hlhs, hrhs]
  rfl

theorem compileExpr_ge_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.ge lhs rhs) =
      Except.ok (YulExpr.call "iszero" [YulExpr.call "lt" [lhsIR, rhsIR]]) := by
  rw [CompilationModel.compileExpr, hlhs, hrhs]
  rfl

theorem compileExpr_le_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.le lhs rhs) =
      Except.ok (YulExpr.call "iszero" [YulExpr.call "gt" [lhsIR, rhsIR]]) := by
  rw [CompilationModel.compileExpr, hlhs, hrhs]
  rfl

theorem compileExpr_logicalNot_ok
    {fields : List Field}
    {expr : Expr}
    {exprIR : YulExpr}
    (hexpr : CompilationModel.compileExpr fields .calldata expr = Except.ok exprIR) :
    CompilationModel.compileExpr fields .calldata (.logicalNot expr) =
      Except.ok (YulExpr.call "iszero" [exprIR]) := by
  rw [CompilationModel.compileExpr, hexpr]
  rfl

theorem compileExpr_logicalAnd_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.logicalAnd lhs rhs) =
      Except.ok (YulExpr.call "and"
        [CompilationModel.yulToBool lhsIR, CompilationModel.yulToBool rhsIR]) := by
  rw [CompilationModel.compileExpr, hlhs, hrhs]
  rfl

theorem compileExpr_logicalOr_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.logicalOr lhs rhs) =
      Except.ok (YulExpr.call "or"
        [CompilationModel.yulToBool lhsIR, CompilationModel.yulToBool rhsIR]) := by
  rw [CompilationModel.compileExpr, hlhs, hrhs]
  rfl

theorem compileExpr_add_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.add lhs rhs) =
      Except.ok (YulExpr.call "add" [lhsIR, rhsIR]) := by
  rw [CompilationModel.compileExpr, hlhs, hrhs]
  rfl

theorem compileExpr_sub_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.sub lhs rhs) =
      Except.ok (YulExpr.call "sub" [lhsIR, rhsIR]) := by
  rw [CompilationModel.compileExpr, hlhs, hrhs]
  rfl

theorem compileExpr_mul_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.mul lhs rhs) =
      Except.ok (YulExpr.call "mul" [lhsIR, rhsIR]) := by
  rw [CompilationModel.compileExpr, hlhs, hrhs]
  rfl

theorem compileExpr_div_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.div lhs rhs) =
      Except.ok (YulExpr.call "div" [lhsIR, rhsIR]) := by
  rw [CompilationModel.compileExpr, hlhs, hrhs]
  rfl

theorem compileExpr_mod_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.mod lhs rhs) =
      Except.ok (YulExpr.call "mod" [lhsIR, rhsIR]) := by
  rw [CompilationModel.compileExpr, hlhs, hrhs]
  rfl

theorem eval_compileExpr_eq_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs))
    (hlhsLt : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhsLt : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.eq lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.eq lhs rhs)) := by
   have hcompile := compileExpr_eq_ok hlhsCompile hrhsCompile
   have heval :
       evalIRExpr state
         (CompilationModel.compileExpr fields .calldata (.eq lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
           some (SourceSemantics.boolWord
             (SourceSemantics.evalExpr fields runtime lhs % Compiler.Constants.evmModulus =
               SourceSemantics.evalExpr fields runtime rhs % Compiler.Constants.evmModulus)) := by
     simpa [hcompile] using evalIRExpr_eq_of_eval hlhsEval hrhsEval
   rw [heval]
   rw [show SourceSemantics.evalExpr fields runtime (.eq lhs rhs) =
       SourceSemantics.boolWord (decide (SourceSemantics.evalExpr fields runtime lhs =
         SourceSemantics.evalExpr fields runtime rhs)) by rfl]
   simp [Nat.mod_eq_of_lt hlhsLt, Nat.mod_eq_of_lt hrhsLt]

theorem eval_compileExpr_lt_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs))
    (hlhsLt : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhsLt : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.lt lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.lt lhs rhs)) := by
   have hcompile := compileExpr_lt_ok hlhsCompile hrhsCompile
   have heval :
       evalIRExpr state
         (CompilationModel.compileExpr fields .calldata (.lt lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
           some (SourceSemantics.boolWord
             (SourceSemantics.evalExpr fields runtime lhs % Compiler.Constants.evmModulus <
               SourceSemantics.evalExpr fields runtime rhs % Compiler.Constants.evmModulus)) := by
     simpa [hcompile] using evalIRExpr_lt_of_eval hlhsEval hrhsEval
   rw [heval]
   rw [show SourceSemantics.evalExpr fields runtime (.lt lhs rhs) =
       SourceSemantics.boolWord (decide (SourceSemantics.evalExpr fields runtime lhs <
         SourceSemantics.evalExpr fields runtime rhs)) by rfl]
   simp [Nat.mod_eq_of_lt hlhsLt, Nat.mod_eq_of_lt hrhsLt]

theorem eval_compileExpr_gt_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs))
    (hlhsLt : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhsLt : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.gt lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.gt lhs rhs)) := by
   have hcompile := compileExpr_gt_ok hlhsCompile hrhsCompile
   have heval :
       evalIRExpr state
         (CompilationModel.compileExpr fields .calldata (.gt lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
           some (SourceSemantics.boolWord
             (SourceSemantics.evalExpr fields runtime rhs % Compiler.Constants.evmModulus <
               SourceSemantics.evalExpr fields runtime lhs % Compiler.Constants.evmModulus)) := by
     simpa [hcompile] using evalIRExpr_gt_of_eval hlhsEval hrhsEval
   rw [heval]
   rw [show SourceSemantics.evalExpr fields runtime (.gt lhs rhs) =
       SourceSemantics.boolWord (decide (SourceSemantics.evalExpr fields runtime rhs <
         SourceSemantics.evalExpr fields runtime lhs)) by rfl]
   simp [Nat.mod_eq_of_lt hlhsLt, Nat.mod_eq_of_lt hrhsLt]

theorem eval_compileExpr_ge_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs))
    (hlhsLt : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhsLt : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.ge lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.ge lhs rhs)) := by
   have hcompile := compileExpr_ge_ok hlhsCompile hrhsCompile
   have hltEval :
       evalIRExpr state (YulExpr.call "lt" [lhsIR, rhsIR]) =
         some (SourceSemantics.boolWord
           (SourceSemantics.evalExpr fields runtime lhs % Compiler.Constants.evmModulus <
             SourceSemantics.evalExpr fields runtime rhs % Compiler.Constants.evmModulus)) := by
     simpa using evalIRExpr_lt_of_eval hlhsEval hrhsEval
   have hinnerLt :
       SourceSemantics.boolWord
         (SourceSemantics.evalExpr fields runtime lhs % Compiler.Constants.evmModulus <
           SourceSemantics.evalExpr fields runtime rhs % Compiler.Constants.evmModulus) <
         Compiler.Constants.evmModulus :=
     boolWord_lt_evmModulus _
   have heval :
       evalIRExpr state
         (CompilationModel.compileExpr fields .calldata (.ge lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
           some (SourceSemantics.boolWord
             (SourceSemantics.boolWord
               (SourceSemantics.evalExpr fields runtime lhs % Compiler.Constants.evmModulus <
                 SourceSemantics.evalExpr fields runtime rhs % Compiler.Constants.evmModulus) = 0)) := by
     simpa [hcompile] using evalIRExpr_iszero_of_lt hltEval hinnerLt
   rw [heval]
   rw [show SourceSemantics.evalExpr fields runtime (.ge lhs rhs) =
       SourceSemantics.boolWord (decide (SourceSemantics.evalExpr fields runtime rhs ≤
         SourceSemantics.evalExpr fields runtime lhs)) by rfl]
   by_cases hlt : SourceSemantics.evalExpr fields runtime lhs < SourceSemantics.evalExpr fields runtime rhs
   · have hnotle : ¬ SourceSemantics.evalExpr fields runtime rhs ≤
       SourceSemantics.evalExpr fields runtime lhs := Nat.not_le_of_gt hlt
     simp [Nat.mod_eq_of_lt hlhsLt, Nat.mod_eq_of_lt hrhsLt, hlt, hnotle, SourceSemantics.boolWord]
   · have hle : SourceSemantics.evalExpr fields runtime rhs ≤
       SourceSemantics.evalExpr fields runtime lhs := Nat.le_of_not_gt hlt
     simp [Nat.mod_eq_of_lt hlhsLt, Nat.mod_eq_of_lt hrhsLt, hlt, hle, SourceSemantics.boolWord]

theorem eval_compileExpr_le_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs))
    (hlhsLt : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhsLt : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.le lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.le lhs rhs)) := by
   have hcompile := compileExpr_le_ok hlhsCompile hrhsCompile
   have hgtEval :
       evalIRExpr state (YulExpr.call "gt" [lhsIR, rhsIR]) =
         some (SourceSemantics.boolWord
           (SourceSemantics.evalExpr fields runtime rhs % Compiler.Constants.evmModulus <
             SourceSemantics.evalExpr fields runtime lhs % Compiler.Constants.evmModulus)) := by
     simpa using evalIRExpr_gt_of_eval hlhsEval hrhsEval
   have hinnerLt :
       SourceSemantics.boolWord
         (SourceSemantics.evalExpr fields runtime rhs % Compiler.Constants.evmModulus <
           SourceSemantics.evalExpr fields runtime lhs % Compiler.Constants.evmModulus) <
         Compiler.Constants.evmModulus :=
     boolWord_lt_evmModulus _
   have heval :
       evalIRExpr state
         (CompilationModel.compileExpr fields .calldata (.le lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
           some (SourceSemantics.boolWord
             (SourceSemantics.boolWord
               (SourceSemantics.evalExpr fields runtime rhs % Compiler.Constants.evmModulus <
                 SourceSemantics.evalExpr fields runtime lhs % Compiler.Constants.evmModulus) = 0)) := by
     simpa [hcompile] using evalIRExpr_iszero_of_lt hgtEval hinnerLt
   rw [heval]
   rw [show SourceSemantics.evalExpr fields runtime (.le lhs rhs) =
       SourceSemantics.boolWord (decide (SourceSemantics.evalExpr fields runtime lhs ≤
         SourceSemantics.evalExpr fields runtime rhs)) by rfl]
   by_cases hgt : SourceSemantics.evalExpr fields runtime rhs < SourceSemantics.evalExpr fields runtime lhs
   · have hnotle : ¬ SourceSemantics.evalExpr fields runtime lhs ≤
       SourceSemantics.evalExpr fields runtime rhs := Nat.not_le_of_gt hgt
     simp [Nat.mod_eq_of_lt hlhsLt, Nat.mod_eq_of_lt hrhsLt, hgt, hnotle, SourceSemantics.boolWord]
   · have hle : SourceSemantics.evalExpr fields runtime lhs ≤
       SourceSemantics.evalExpr fields runtime rhs := Nat.le_of_not_gt hgt
     simp [Nat.mod_eq_of_lt hlhsLt, Nat.mod_eq_of_lt hrhsLt, hgt, hle, SourceSemantics.boolWord]

theorem eval_compileExpr_logicalNot_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {expr : Expr}
    {exprIR : YulExpr}
    (hexprCompile : CompilationModel.compileExpr fields .calldata expr = Except.ok exprIR)
    (hexprEval : evalIRExpr state exprIR = some (SourceSemantics.evalExpr fields runtime expr))
    (hexprLt : SourceSemantics.evalExpr fields runtime expr < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.logicalNot expr) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.logicalNot expr)) := by
   have hcompile := compileExpr_logicalNot_ok hexprCompile
   have heval :
       evalIRExpr state
         (CompilationModel.compileExpr fields .calldata (.logicalNot expr) |>.toOption.getD (YulExpr.lit 0)) =
           some (SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime expr = 0)) := by
     simpa [hcompile] using evalIRExpr_iszero_of_lt hexprEval hexprLt
   rw [heval]
   rw [show SourceSemantics.evalExpr fields runtime (.logicalNot expr) =
       SourceSemantics.boolWord (decide (SourceSemantics.evalExpr fields runtime expr = 0)) by rfl]

theorem eval_compileExpr_logicalAnd_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs))
    (hlhsLt : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhsLt : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.logicalAnd lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.logicalAnd lhs rhs)) := by
   have hcompile := compileExpr_logicalAnd_ok hlhsCompile hrhsCompile
   have hlhsBool :
       evalIRExpr state (CompilationModel.yulToBool lhsIR) =
         some (SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime lhs ≠ 0)) := by
     simpa using evalIRExpr_yulToBool_of_lt hlhsEval hlhsLt
   have hrhsBool :
       evalIRExpr state (CompilationModel.yulToBool rhsIR) =
         some (SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime rhs ≠ 0)) := by
     simpa using evalIRExpr_yulToBool_of_lt hrhsEval hrhsLt
   have hcall :
       evalIRExpr state
         (YulExpr.call "and" [CompilationModel.yulToBool lhsIR, CompilationModel.yulToBool rhsIR]) =
           some ((SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime lhs ≠ 0)) &&&
             (SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime rhs ≠ 0))) := by
     simpa only
       [Nat.mod_eq_of_lt (boolWord_lt_evmModulus (decide (SourceSemantics.evalExpr fields runtime lhs ≠ 0))),
       Nat.mod_eq_of_lt (boolWord_lt_evmModulus (decide (SourceSemantics.evalExpr fields runtime rhs ≠ 0)))] using
       evalIRExpr_and_of_eval hlhsBool hrhsBool
   have heval :
       evalIRExpr state
         (CompilationModel.compileExpr fields .calldata (.logicalAnd lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
           some ((SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime lhs ≠ 0)) &&&
             (SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime rhs ≠ 0))) := by
     simpa [hcompile] using hcall
   rw [heval]
   congr
   rw [boolWord_and]
   rw [show SourceSemantics.evalExpr fields runtime (.logicalAnd lhs rhs) =
       SourceSemantics.boolWord
         (decide (SourceSemantics.evalExpr fields runtime lhs != 0) &&
           decide (SourceSemantics.evalExpr fields runtime rhs != 0)) by
       rfl]
   by_cases hlhsZero : SourceSemantics.evalExpr fields runtime lhs = 0
   · by_cases hrhsZero : SourceSemantics.evalExpr fields runtime rhs = 0
     · simp [hlhsZero, hrhsZero, SourceSemantics.boolWord]
     · simp [hlhsZero, hrhsZero, SourceSemantics.boolWord]
   · by_cases hrhsZero : SourceSemantics.evalExpr fields runtime rhs = 0
     · simp [hlhsZero, hrhsZero, SourceSemantics.boolWord]
     · simp [hlhsZero, hrhsZero, SourceSemantics.boolWord]

theorem eval_compileExpr_logicalOr_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs))
    (hlhsLt : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhsLt : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.logicalOr lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.logicalOr lhs rhs)) := by
   have hcompile := compileExpr_logicalOr_ok hlhsCompile hrhsCompile
   have hlhsBool :
       evalIRExpr state (CompilationModel.yulToBool lhsIR) =
         some (SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime lhs ≠ 0)) := by
     simpa using evalIRExpr_yulToBool_of_lt hlhsEval hlhsLt
   have hrhsBool :
       evalIRExpr state (CompilationModel.yulToBool rhsIR) =
         some (SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime rhs ≠ 0)) := by
     simpa using evalIRExpr_yulToBool_of_lt hrhsEval hrhsLt
   have hcall :
       evalIRExpr state
         (YulExpr.call "or" [CompilationModel.yulToBool lhsIR, CompilationModel.yulToBool rhsIR]) =
           some ((SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime lhs ≠ 0)) |||
             (SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime rhs ≠ 0))) := by
     simpa only
       [Nat.mod_eq_of_lt (boolWord_lt_evmModulus (decide (SourceSemantics.evalExpr fields runtime lhs ≠ 0))),
       Nat.mod_eq_of_lt (boolWord_lt_evmModulus (decide (SourceSemantics.evalExpr fields runtime rhs ≠ 0)))] using
       evalIRExpr_or_of_eval hlhsBool hrhsBool
   have heval :
       evalIRExpr state
         (CompilationModel.compileExpr fields .calldata (.logicalOr lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
           some ((SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime lhs ≠ 0)) |||
             (SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime rhs ≠ 0))) := by
     simpa [hcompile] using hcall
   rw [heval]
   congr
   rw [boolWord_or]
   rw [show SourceSemantics.evalExpr fields runtime (.logicalOr lhs rhs) =
       SourceSemantics.boolWord
         (decide (SourceSemantics.evalExpr fields runtime lhs != 0) ||
           decide (SourceSemantics.evalExpr fields runtime rhs != 0)) by
       rfl]
   by_cases hlhsZero : SourceSemantics.evalExpr fields runtime lhs = 0
   · by_cases hrhsZero : SourceSemantics.evalExpr fields runtime rhs = 0
     · simp [hlhsZero, hrhsZero, SourceSemantics.boolWord]
     · simp [hlhsZero, hrhsZero, SourceSemantics.boolWord]
   · by_cases hrhsZero : SourceSemantics.evalExpr fields runtime rhs = 0
     · simp [hlhsZero, hrhsZero, SourceSemantics.boolWord]
     · simp [hlhsZero, hrhsZero, SourceSemantics.boolWord]

theorem eval_compileExpr_add_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs)) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.add lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.add lhs rhs)) := by
   have hcompile := compileExpr_add_ok hlhsCompile hrhsCompile
   have heval :
       evalIRExpr state
         (CompilationModel.compileExpr fields .calldata (.add lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
           some ((SourceSemantics.evalExpr fields runtime lhs +
             SourceSemantics.evalExpr fields runtime rhs) % Compiler.Constants.evmModulus) := by
     simpa [hcompile] using evalIRExpr_add_of_eval hlhsEval hrhsEval
   rw [heval]
   refine congrArg some ?_
   change
     ((SourceSemantics.evalExpr fields runtime lhs + SourceSemantics.evalExpr fields runtime rhs) %
       Compiler.Constants.evmModulus) =
     (((SourceSemantics.evalExpr fields runtime lhs : Verity.Core.Uint256) +
       (SourceSemantics.evalExpr fields runtime rhs : Verity.Core.Uint256)) : Verity.Core.Uint256).val
   rw [Nat.add_mod]
   simp [HAdd.hAdd, Verity.Core.Uint256.add, Verity.Core.Uint256.ofNat,
     Verity.Core.Uint256.modulus, Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS]

theorem eval_compileExpr_mul_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs)) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.mul lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.mul lhs rhs)) := by
   have hcompile := compileExpr_mul_ok hlhsCompile hrhsCompile
   have heval :
       evalIRExpr state
         (CompilationModel.compileExpr fields .calldata (.mul lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
           some ((SourceSemantics.evalExpr fields runtime lhs *
             SourceSemantics.evalExpr fields runtime rhs) % Compiler.Constants.evmModulus) := by
     simpa [hcompile] using evalIRExpr_mul_of_eval hlhsEval hrhsEval
   rw [heval]
   refine congrArg some ?_
   change
     ((SourceSemantics.evalExpr fields runtime lhs * SourceSemantics.evalExpr fields runtime rhs) %
       Compiler.Constants.evmModulus) =
     (((SourceSemantics.evalExpr fields runtime lhs : Verity.Core.Uint256) *
       (SourceSemantics.evalExpr fields runtime rhs : Verity.Core.Uint256)) : Verity.Core.Uint256).val
   rw [Nat.mul_mod]
   simp [HMul.hMul, Verity.Core.Uint256.mul, Verity.Core.Uint256.ofNat,
     Verity.Core.Uint256.modulus, Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS]

/-- Bridge `Nat` values already known to be in-range to their `Uint256` coercion. -/
theorem uint256_val_ofNat_eq
    {n : Nat}
    (hn : n < Compiler.Constants.evmModulus) :
    ((n : Verity.Core.Uint256)).val = n := by
  rw [show ((n : Verity.Core.Uint256)).val = n % Compiler.Constants.evmModulus by rfl]
  exact Nat.mod_eq_of_lt hn

/-- Division on in-range `Nat` values agrees with `Uint256.div`. -/
theorem uint256_div_val_eq
    {a b : Nat}
    (ha : a < Compiler.Constants.evmModulus)
    (hb : b < Compiler.Constants.evmModulus) :
    (((a : Verity.Core.Uint256) / (b : Verity.Core.Uint256)) : Verity.Core.Uint256).val =
      if b = 0 then 0 else a / b := by
  by_cases hzero : b = 0
  · subst hzero
    simp [HDiv.hDiv, Verity.Core.Uint256.div, Verity.Core.Uint256.ofNat]
  · have hdivLt : a / b < Compiler.Constants.evmModulus := by
      exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha
    have hdivMod : (a / b) % Compiler.Constants.evmModulus = a / b :=
      Nat.mod_eq_of_lt hdivLt
    simpa [HDiv.hDiv, Verity.Core.Uint256.div, Verity.Core.Uint256.ofNat,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, hzero] using hdivMod

/-- Subtraction on in-range `Nat` values agrees with `Uint256.sub`. -/
theorem uint256_sub_val_eq
    {a b : Nat}
    (ha : a < Compiler.Constants.evmModulus)
    (hb : b < Compiler.Constants.evmModulus) :
    (((a : Verity.Core.Uint256) - (b : Verity.Core.Uint256)) : Verity.Core.Uint256).val =
      (Compiler.Constants.evmModulus + a - b) % Compiler.Constants.evmModulus := by
  change (Verity.Core.Uint256.sub (a : Verity.Core.Uint256) (b : Verity.Core.Uint256)).val =
    (Compiler.Constants.evmModulus + a - b) % Compiler.Constants.evmModulus
  by_cases hle : b ≤ a
  · have hsubLt : a - b < Compiler.Constants.evmModulus := by
      exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) ha
    have hsum : Compiler.Constants.evmModulus + a - b =
        Compiler.Constants.evmModulus + (a - b) := by
      omega
    simp [Verity.Core.Uint256.sub, Verity.Core.Uint256.ofNat,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, hle]
    rw [hsum]
    simpa [Nat.mod_eq_of_lt hsubLt] using
      Nat.add_mod_right_right (a - b) Compiler.Constants.evmModulus
  · have hgt : b > a := Nat.lt_of_not_ge hle
    have hsubLt : a - b < Compiler.Constants.evmModulus := by
      exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) ha
    have hdiffPos : 0 < b - a := Nat.sub_pos_of_lt hgt
    have hdiffLe : b - a ≤ Compiler.Constants.evmModulus := by
      exact Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hb)
    have hdiffLt : Compiler.Constants.evmModulus - (b - a) < Compiler.Constants.evmModulus := by
      omega
    have hsum : Compiler.Constants.evmModulus + a - b =
        Compiler.Constants.evmModulus - (b - a) := by
      omega
    simp [Verity.Core.Uint256.sub, Verity.Core.Uint256.ofNat,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, hle, hsum, Nat.mod_eq_of_lt hdiffLt]

/-- Modulo on in-range `Nat` values agrees with `Uint256.mod`. -/
theorem uint256_mod_val_eq
    {a b : Nat}
    (ha : a < Compiler.Constants.evmModulus)
    (hb : b < Compiler.Constants.evmModulus) :
    (((a : Verity.Core.Uint256) % (b : Verity.Core.Uint256)) : Verity.Core.Uint256).val =
      if b = 0 then 0 else a % b := by
  change (Verity.Core.Uint256.mod (a : Verity.Core.Uint256) (b : Verity.Core.Uint256)).val =
    if b = 0 then 0 else a % b
  by_cases hzero : b = 0
  · subst hzero
    simp [Verity.Core.Uint256.mod, Verity.Core.Uint256.ofNat]
  · have hbpos : 0 < b := Nat.pos_of_ne_zero hzero
    have hmodLt : a % b < Compiler.Constants.evmModulus := by
      exact Nat.lt_trans (Nat.mod_lt _ hbpos) hb
    simp [Verity.Core.Uint256.mod, Verity.Core.Uint256.ofNat]
    rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
    simp [hzero, Nat.mod_eq_of_lt hmodLt]

theorem eval_compileExpr_div_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs))
    (hlhsLt : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhsLt : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.div lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.div lhs rhs)) := by
   have hcompile := compileExpr_div_ok hlhsCompile hrhsCompile
   have heval :
       evalIRExpr state
         (CompilationModel.compileExpr fields .calldata (.div lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
           some (if SourceSemantics.evalExpr fields runtime rhs % Compiler.Constants.evmModulus = 0 then 0
             else
               (SourceSemantics.evalExpr fields runtime lhs % Compiler.Constants.evmModulus) /
                 (SourceSemantics.evalExpr fields runtime rhs % Compiler.Constants.evmModulus)) := by
     simpa [hcompile] using evalIRExpr_div_of_eval hlhsEval hrhsEval
   rw [heval]
   rw [show SourceSemantics.evalExpr fields runtime (.div lhs rhs) =
       (((SourceSemantics.evalExpr fields runtime lhs : Verity.Core.Uint256) /
         (SourceSemantics.evalExpr fields runtime rhs : Verity.Core.Uint256)) : Verity.Core.Uint256).val by
       rfl]
   rw [uint256_div_val_eq hlhsLt hrhsLt]
   simp [Nat.mod_eq_of_lt hlhsLt, Nat.mod_eq_of_lt hrhsLt]

theorem eval_compileExpr_sub_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs))
    (hlhsLt : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhsLt : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.sub lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.sub lhs rhs)) := by
   have hcompile := compileExpr_sub_ok hlhsCompile hrhsCompile
   have heval :
       evalIRExpr state
         (CompilationModel.compileExpr fields .calldata (.sub lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
           some ((Compiler.Constants.evmModulus +
             (SourceSemantics.evalExpr fields runtime lhs % Compiler.Constants.evmModulus) -
             (SourceSemantics.evalExpr fields runtime rhs % Compiler.Constants.evmModulus)) %
               Compiler.Constants.evmModulus) := by
     simpa [hcompile] using evalIRExpr_sub_of_eval hlhsEval hrhsEval
   rw [heval]
   rw [show SourceSemantics.evalExpr fields runtime (.sub lhs rhs) =
       (((SourceSemantics.evalExpr fields runtime lhs : Verity.Core.Uint256) -
         (SourceSemantics.evalExpr fields runtime rhs : Verity.Core.Uint256)) : Verity.Core.Uint256).val by
       rfl]
   rw [uint256_sub_val_eq hlhsLt hrhsLt]
   simp [Nat.mod_eq_of_lt hlhsLt, Nat.mod_eq_of_lt hrhsLt]

theorem eval_compileExpr_mod_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs))
    (hlhsLt : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhsLt : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.mod lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.mod lhs rhs)) := by
   have hcompile := compileExpr_mod_ok hlhsCompile hrhsCompile
   have heval :
       evalIRExpr state
         (CompilationModel.compileExpr fields .calldata (.mod lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
           some (if SourceSemantics.evalExpr fields runtime rhs % Compiler.Constants.evmModulus = 0 then 0
             else
               (SourceSemantics.evalExpr fields runtime lhs % Compiler.Constants.evmModulus) %
                 (SourceSemantics.evalExpr fields runtime rhs % Compiler.Constants.evmModulus)) := by
     simpa [hcompile] using evalIRExpr_mod_of_eval hlhsEval hrhsEval
   rw [heval]
   rw [show SourceSemantics.evalExpr fields runtime (.mod lhs rhs) =
       (((SourceSemantics.evalExpr fields runtime lhs : Verity.Core.Uint256) %
         (SourceSemantics.evalExpr fields runtime rhs : Verity.Core.Uint256)) : Verity.Core.Uint256).val by
       rfl]
   rw [uint256_mod_val_eq hlhsLt hrhsLt]
   simp [Nat.mod_eq_of_lt hlhsLt, Nat.mod_eq_of_lt hrhsLt]

theorem evalExpr_literal_lt_evmModulus
    (fields : List Field)
    (state : SourceSemantics.RuntimeState)
    (value : Nat) :
    SourceSemantics.evalExpr fields state (.literal value) < Compiler.Constants.evmModulus := by
  change SourceSemantics.wordNormalize value < Compiler.Constants.evmModulus
  exact wordNormalize_lt_evmModulus value

theorem evalExpr_param_lt_evmModulus_of_bindingsBounded
    (fields : List Field)
    (state : SourceSemantics.RuntimeState)
    (name : String)
    (hbounded : bindingsBounded state.bindings) :
    SourceSemantics.evalExpr fields state (.param name) < Compiler.Constants.evmModulus := by
  change SourceSemantics.lookupValue state.bindings name < Compiler.Constants.evmModulus
  exact hbounded name

theorem evalExpr_localVar_lt_evmModulus_of_bindingsBounded
    (fields : List Field)
    (state : SourceSemantics.RuntimeState)
    (name : String)
    (hbounded : bindingsBounded state.bindings) :
    SourceSemantics.evalExpr fields state (.localVar name) < Compiler.Constants.evmModulus := by
  change SourceSemantics.lookupValue state.bindings name < Compiler.Constants.evmModulus
  exact hbounded name

theorem exprBoundNamesPresent_of_subset
    {expr subexpr : Expr}
    {bindings : List (String × Nat)}
    (hpresent : exprBoundNamesPresent expr bindings)
    (hsubset : ∀ name, name ∈ exprBoundNames subexpr → name ∈ exprBoundNames expr) :
    exprBoundNamesPresent subexpr bindings := by
  intro name hmem
  exact hpresent name (hsubset name hmem)

-- ExprCompileCore is now in ExprCore.lean

theorem compileExpr_core_ok
    {fields : List Field}
    {expr : Expr}
    (hcore : ExprCompileCore expr) :
    ∃ exprIR, CompilationModel.compileExpr fields .calldata expr = Except.ok exprIR := by
  induction hcore with
  | literal value =>
      exact ⟨YulExpr.lit (value % CompilationModel.uint256Modulus), rfl⟩
  | param name =>
      exact ⟨YulExpr.ident name, rfl⟩
  | localVar name =>
      exact ⟨YulExpr.ident name, rfl⟩
  | caller =>
      exact ⟨YulExpr.call "caller" [], rfl⟩
  | contractAddress =>
      exact ⟨YulExpr.call "address" [], rfl⟩
  | msgValue =>
      exact ⟨YulExpr.call "callvalue" [], rfl⟩
  | blockTimestamp =>
      exact ⟨YulExpr.call "timestamp" [], rfl⟩
  | blockNumber =>
      exact ⟨YulExpr.call "number" [], rfl⟩
  | chainid =>
      exact ⟨YulExpr.call "chainid" [], rfl⟩
  | add hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "add" [lhsIR, rhsIR], compileExpr_add_ok hlhs hrhs⟩
  | sub hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "sub" [lhsIR, rhsIR], compileExpr_sub_ok hlhs hrhs⟩
  | mul hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "mul" [lhsIR, rhsIR], compileExpr_mul_ok hlhs hrhs⟩
  | div hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "div" [lhsIR, rhsIR], compileExpr_div_ok hlhs hrhs⟩
  | mod hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "mod" [lhsIR, rhsIR], compileExpr_mod_ok hlhs hrhs⟩
  | eq hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "eq" [lhsIR, rhsIR], compileExpr_eq_ok hlhs hrhs⟩
  | lt hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "lt" [lhsIR, rhsIR], compileExpr_lt_ok hlhs hrhs⟩
  | gt hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "gt" [lhsIR, rhsIR], compileExpr_gt_ok hlhs hrhs⟩
  | ge hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "lt" [lhsIR, rhsIR]], compileExpr_ge_ok hlhs hrhs⟩
  | le hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "gt" [lhsIR, rhsIR]], compileExpr_le_ok hlhs hrhs⟩
  | logicalNot h ih =>
      rename_i expr
      rcases ih with ⟨exprIR, hexpr⟩
      exact ⟨YulExpr.call "iszero" [exprIR], compileExpr_logicalNot_ok hexpr⟩
  | logicalAnd hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "and"
          [CompilationModel.yulToBool lhsIR, CompilationModel.yulToBool rhsIR],
        compileExpr_logicalAnd_ok hlhs hrhs⟩
  | logicalOr hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "or"
          [CompilationModel.yulToBool lhsIR, CompilationModel.yulToBool rhsIR],
        compileExpr_logicalOr_ok hlhs hrhs⟩

mutual
theorem eval_compileExpr_core_onExpr
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {expr : Expr}
    (hcore : ExprCompileCore expr)
    (hexact : bindingsExactlyMatchIRVarsOnExpr expr runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hpresent : exprBoundNamesPresent expr runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata expr |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime expr) := by
  induction hcore generalizing runtime state with
  | literal value =>
      simpa [CompilationModel.compileExpr] using eval_compileExpr_literal fields runtime state value
  | param name =>
      simpa [CompilationModel.compileExpr] using
        eval_compileExpr_param_of_expr_bindings name hexact hpresent
  | localVar name =>
      simpa [CompilationModel.compileExpr] using
        eval_compileExpr_localVar_of_expr_bindings name hexact hpresent
  | caller =>
      exact eval_compileExpr_caller hruntime
  | contractAddress =>
      exact eval_compileExpr_contractAddress hruntime
  | msgValue =>
      exact eval_compileExpr_msgValue hruntime
  | blockTimestamp =>
      exact eval_compileExpr_blockTimestamp hruntime
  | blockNumber =>
      exact eval_compileExpr_blockNumber hruntime
  | chainid =>
      exact eval_compileExpr_chainid hruntime
  | add hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime
        rw [hlhs] at htmp
        simpa using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime
        rw [hrhs] at htmp
        simpa using htmp
      exact eval_compileExpr_add_of_compiled hlhs hrhs
        hEvalL hEvalR
  | sub hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime
        rw [hlhs] at htmp
        simpa using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime
        rw [hrhs] at htmp
        simpa using htmp
      exact eval_compileExpr_sub_of_compiled hlhs hrhs
        hEvalL hEvalR
        (evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime)
  | mul hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime
        rw [hlhs] at htmp
        simpa using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime
        rw [hrhs] at htmp
        simpa using htmp
      exact eval_compileExpr_mul_of_compiled hlhs hrhs
        hEvalL hEvalR
  | div hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime
        rw [hlhs] at htmp
        simpa using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime
        rw [hrhs] at htmp
        simpa using htmp
      exact eval_compileExpr_div_of_compiled hlhs hrhs
        hEvalL hEvalR
        (evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime)
  | mod hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime
        rw [hlhs] at htmp
        simpa using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime
        rw [hrhs] at htmp
        simpa using htmp
      exact eval_compileExpr_mod_of_compiled hlhs hrhs
        hEvalL hEvalR
        (evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime)
  | eq hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime
        rw [hlhs] at htmp
        simpa using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime
        rw [hrhs] at htmp
        simpa using htmp
      exact eval_compileExpr_eq_of_compiled hlhs hrhs
        hEvalL hEvalR
        (evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime)
  | lt hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime
        rw [hlhs] at htmp
        simpa using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime
        rw [hrhs] at htmp
        simpa using htmp
      exact eval_compileExpr_lt_of_compiled hlhs hrhs
        hEvalL hEvalR
        (evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime)
  | gt hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime
        rw [hlhs] at htmp
        simpa using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime
        rw [hrhs] at htmp
        simpa using htmp
      exact eval_compileExpr_gt_of_compiled hlhs hrhs
        hEvalL hEvalR
        (evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime)
  | ge hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime
        rw [hlhs] at htmp
        simpa using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime
        rw [hrhs] at htmp
        simpa using htmp
      exact eval_compileExpr_ge_of_compiled hlhs hrhs
        hEvalL hEvalR
        (evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime)
  | le hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime
        rw [hlhs] at htmp
        simpa using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime
        rw [hrhs] at htmp
        simpa using htmp
      exact eval_compileExpr_le_of_compiled hlhs hrhs
        hEvalL hEvalR
        (evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime)
  | logicalNot h ih =>
      rename_i expr
      rcases compileExpr_core_ok h with ⟨exprIR, hexpr⟩
      have hexact' : bindingsExactlyMatchIRVarsOnExpr expr runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using hmem)
      have hpresent' := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using hmem)
      have hEval : evalIRExpr state exprIR = some (SourceSemantics.evalExpr fields runtime expr) := by
        have htmp := ih hexact' hbounded hpresent' hruntime
        rw [hexpr] at htmp
        simpa using htmp
      exact eval_compileExpr_logicalNot_of_compiled hexpr
        hEval
        (evalExpr_lt_evmModulus_core_onExpr h hexact' hbounded hpresent' hruntime)
  | logicalAnd hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime
        rw [hlhs] at htmp
        simpa using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime
        rw [hrhs] at htmp
        simpa using htmp
      exact eval_compileExpr_logicalAnd_of_compiled hlhs hrhs
        hEvalL hEvalR
        (evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime)
  | logicalOr hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime
        rw [hlhs] at htmp
        simpa using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime
        rw [hrhs] at htmp
        simpa using htmp
      exact eval_compileExpr_logicalOr_of_compiled hlhs hrhs
        hEvalL hEvalR
        (evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime)

theorem eval_compileExpr_core
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {expr : Expr}
    (hcore : ExprCompileCore expr)
    (hexact : bindingsExactlyMatchIRVars runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hpresent : exprBoundNamesPresent expr runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata expr |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime expr) :=
  eval_compileExpr_core_onExpr hcore
    (bindingsExactlyMatchIRVars_implies_onExpr hexact) hbounded hpresent hruntime

theorem evalExpr_lt_evmModulus_core_onExpr
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {expr : Expr}
    (hcore : ExprCompileCore expr)
    (hexact : bindingsExactlyMatchIRVarsOnExpr expr runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hpresent : exprBoundNamesPresent expr runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    SourceSemantics.evalExpr fields runtime expr < Compiler.Constants.evmModulus := by
   induction hcore generalizing runtime state with
   | literal value =>
       exact evalExpr_literal_lt_evmModulus fields runtime value
   | param name =>
       exact evalExpr_param_lt_evmModulus_of_bindingsBounded fields runtime name hbounded
   | localVar name =>
       exact evalExpr_localVar_lt_evmModulus_of_bindingsBounded fields runtime name hbounded
   | caller =>
       have haddrLt : runtime.world.sender.val < Verity.Core.ADDRESS_MODULUS := by
         simpa [Verity.Core.Address.modulus] using
           Verity.Core.Address.val_lt_modulus runtime.world.sender
       have hmodLt : Verity.Core.ADDRESS_MODULUS < Compiler.Constants.evmModulus := by
         norm_num [Verity.Core.ADDRESS_MODULUS, Compiler.Constants.evmModulus]
       change runtime.world.sender.val < Compiler.Constants.evmModulus
       exact Nat.lt_trans haddrLt hmodLt
   | contractAddress =>
       have haddrLt : runtime.world.thisAddress.val < Verity.Core.ADDRESS_MODULUS := by
         simpa [Verity.Core.Address.modulus] using
           Verity.Core.Address.val_lt_modulus runtime.world.thisAddress
       have hmodLt : Verity.Core.ADDRESS_MODULUS < Compiler.Constants.evmModulus := by
         norm_num [Verity.Core.ADDRESS_MODULUS, Compiler.Constants.evmModulus]
       change runtime.world.thisAddress.val < Compiler.Constants.evmModulus
       exact Nat.lt_trans haddrLt hmodLt
   | msgValue =>
       change runtime.world.msgValue.val < Compiler.Constants.evmModulus
       simpa [Verity.Core.Uint256.modulus, Compiler.Constants.evmModulus] using runtime.world.msgValue.isLt
   | blockTimestamp =>
       change runtime.world.blockTimestamp.val < Compiler.Constants.evmModulus
       simpa [Verity.Core.Uint256.modulus, Compiler.Constants.evmModulus] using runtime.world.blockTimestamp.isLt
   | blockNumber =>
       change runtime.world.blockNumber.val < Compiler.Constants.evmModulus
       simpa [Verity.Core.Uint256.modulus, Compiler.Constants.evmModulus] using runtime.world.blockNumber.isLt
   | chainid =>
       change runtime.world.chainId.val < Compiler.Constants.evmModulus
       simpa [Verity.Core.Uint256.modulus, Compiler.Constants.evmModulus] using runtime.world.chainId.isLt
   | add hL hR ihL ihR =>
       rename_i lhs rhs
       change
         ((((SourceSemantics.evalExpr fields runtime lhs : Verity.Core.Uint256) +
           (SourceSemantics.evalExpr fields runtime rhs : Verity.Core.Uint256)) :
             Verity.Core.Uint256)).val < Compiler.Constants.evmModulus
       simpa [Verity.Core.Uint256.modulus, Compiler.Constants.evmModulus] using
         ((((SourceSemantics.evalExpr fields runtime lhs : Verity.Core.Uint256) +
           (SourceSemantics.evalExpr fields runtime rhs : Verity.Core.Uint256)) :
             Verity.Core.Uint256)).isLt
   | sub hL hR ihL ihR =>
       rename_i lhs rhs
       change
         ((((SourceSemantics.evalExpr fields runtime lhs : Verity.Core.Uint256) -
           (SourceSemantics.evalExpr fields runtime rhs : Verity.Core.Uint256)) :
             Verity.Core.Uint256)).val < Compiler.Constants.evmModulus
       simpa [Verity.Core.Uint256.modulus, Compiler.Constants.evmModulus] using
         ((((SourceSemantics.evalExpr fields runtime lhs : Verity.Core.Uint256) -
           (SourceSemantics.evalExpr fields runtime rhs : Verity.Core.Uint256)) :
             Verity.Core.Uint256)).isLt
   | mul hL hR ihL ihR =>
       rename_i lhs rhs
       change
         ((((SourceSemantics.evalExpr fields runtime lhs : Verity.Core.Uint256) *
           (SourceSemantics.evalExpr fields runtime rhs : Verity.Core.Uint256)) :
             Verity.Core.Uint256)).val < Compiler.Constants.evmModulus
       simpa [Verity.Core.Uint256.modulus, Compiler.Constants.evmModulus] using
         ((((SourceSemantics.evalExpr fields runtime lhs : Verity.Core.Uint256) *
           (SourceSemantics.evalExpr fields runtime rhs : Verity.Core.Uint256)) :
             Verity.Core.Uint256)).isLt
   | div hL hR ihL ihR =>
       rename_i lhs rhs
       change
         ((((SourceSemantics.evalExpr fields runtime lhs : Verity.Core.Uint256) /
           (SourceSemantics.evalExpr fields runtime rhs : Verity.Core.Uint256)) :
             Verity.Core.Uint256)).val < Compiler.Constants.evmModulus
       simpa [Verity.Core.Uint256.modulus, Compiler.Constants.evmModulus] using
         ((((SourceSemantics.evalExpr fields runtime lhs : Verity.Core.Uint256) /
           (SourceSemantics.evalExpr fields runtime rhs : Verity.Core.Uint256)) :
             Verity.Core.Uint256)).isLt
   | mod hL hR ihL ihR =>
       rename_i lhs rhs
       change
         ((((SourceSemantics.evalExpr fields runtime lhs : Verity.Core.Uint256) %
           (SourceSemantics.evalExpr fields runtime rhs : Verity.Core.Uint256)) :
             Verity.Core.Uint256)).val < Compiler.Constants.evmModulus
       simpa [Verity.Core.Uint256.modulus, Compiler.Constants.evmModulus] using
         ((((SourceSemantics.evalExpr fields runtime lhs : Verity.Core.Uint256) %
           (SourceSemantics.evalExpr fields runtime rhs : Verity.Core.Uint256)) :
             Verity.Core.Uint256)).isLt
   | eq hL hR ihL ihR =>
       rename_i lhs rhs
       rw [show SourceSemantics.evalExpr fields runtime (.eq lhs rhs) =
           SourceSemantics.boolWord (decide (SourceSemantics.evalExpr fields runtime lhs =
             SourceSemantics.evalExpr fields runtime rhs)) by rfl]
       exact boolWord_lt_evmModulus _
   | lt hL hR ihL ihR =>
       rename_i lhs rhs
       rw [show SourceSemantics.evalExpr fields runtime (.lt lhs rhs) =
           SourceSemantics.boolWord (decide (SourceSemantics.evalExpr fields runtime lhs <
             SourceSemantics.evalExpr fields runtime rhs)) by rfl]
       exact boolWord_lt_evmModulus _
   | gt hL hR ihL ihR =>
       rename_i lhs rhs
       rw [show SourceSemantics.evalExpr fields runtime (.gt lhs rhs) =
           SourceSemantics.boolWord (decide (SourceSemantics.evalExpr fields runtime rhs <
             SourceSemantics.evalExpr fields runtime lhs)) by rfl]
       exact boolWord_lt_evmModulus _
   | ge hL hR ihL ihR =>
       rename_i lhs rhs
       rw [show SourceSemantics.evalExpr fields runtime (.ge lhs rhs) =
           SourceSemantics.boolWord (decide (SourceSemantics.evalExpr fields runtime rhs ≤
             SourceSemantics.evalExpr fields runtime lhs)) by rfl]
       exact boolWord_lt_evmModulus _
   | le hL hR ihL ihR =>
       rename_i lhs rhs
       rw [show SourceSemantics.evalExpr fields runtime (.le lhs rhs) =
           SourceSemantics.boolWord (decide (SourceSemantics.evalExpr fields runtime lhs ≤
             SourceSemantics.evalExpr fields runtime rhs)) by rfl]
       exact boolWord_lt_evmModulus _
   | logicalNot h ih =>
       rename_i expr
       rw [show SourceSemantics.evalExpr fields runtime (.logicalNot expr) =
           SourceSemantics.boolWord (decide (SourceSemantics.evalExpr fields runtime expr = 0)) by rfl]
       exact boolWord_lt_evmModulus _
   | logicalAnd hL hR ihL ihR =>
       rename_i lhs rhs
       rw [show SourceSemantics.evalExpr fields runtime (.logicalAnd lhs rhs) =
           SourceSemantics.boolWord
             (decide (SourceSemantics.evalExpr fields runtime lhs != 0) &&
               decide (SourceSemantics.evalExpr fields runtime rhs != 0)) by rfl]
       exact boolWord_lt_evmModulus _
   | logicalOr hL hR ihL ihR =>
       rename_i lhs rhs
       rw [show SourceSemantics.evalExpr fields runtime (.logicalOr lhs rhs) =
           SourceSemantics.boolWord
             (decide (SourceSemantics.evalExpr fields runtime lhs != 0) ||
               decide (SourceSemantics.evalExpr fields runtime rhs != 0)) by rfl]
       exact boolWord_lt_evmModulus _
end

theorem evalExpr_lt_evmModulus_core
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {expr : Expr}
    (hcore : ExprCompileCore expr)
    (hexact : bindingsExactlyMatchIRVars runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hpresent : exprBoundNamesPresent expr runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    SourceSemantics.evalExpr fields runtime expr < Compiler.Constants.evmModulus :=
  evalExpr_lt_evmModulus_core_onExpr hcore
    (bindingsExactlyMatchIRVars_implies_onExpr hexact) hbounded hpresent hruntime


theorem compileRequireFailCond_core_ok
    {fields : List Field}
    {cond : Expr}
    (hcore : ExprCompileCore cond) :
    ∃ failCond,
      CompilationModel.compileRequireFailCond fields .calldata cond = Except.ok failCond := by
  cases hcore with
  | literal value =>
      exact ⟨YulExpr.call "iszero" [YulExpr.lit (value % CompilationModel.uint256Modulus)], rfl⟩
  | param name =>
      exact ⟨YulExpr.call "iszero" [YulExpr.ident name], rfl⟩
  | localVar name =>
      exact ⟨YulExpr.call "iszero" [YulExpr.ident name], rfl⟩
  | caller =>
      exact ⟨YulExpr.call "iszero" [YulExpr.call "caller" []], rfl⟩
  | contractAddress =>
      exact ⟨YulExpr.call "iszero" [YulExpr.call "address" []], rfl⟩
  | msgValue =>
      exact ⟨YulExpr.call "iszero" [YulExpr.call "callvalue" []], rfl⟩
  | blockTimestamp =>
      exact ⟨YulExpr.call "iszero" [YulExpr.call "timestamp" []], rfl⟩
  | blockNumber =>
      exact ⟨YulExpr.call "iszero" [YulExpr.call "number" []], rfl⟩
  | chainid =>
      exact ⟨YulExpr.call "iszero" [YulExpr.call "chainid" []], rfl⟩
  | add hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "add" [lhsIR, rhsIR]], by
        rw [CompilationModel.compileRequireFailCond, compileExpr_add_ok hlhs hrhs]
        all_goals
          try rfl
          try
            intro a b hEq
            cases hEq⟩
  | sub hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "sub" [lhsIR, rhsIR]], by
        rw [CompilationModel.compileRequireFailCond, compileExpr_sub_ok hlhs hrhs]
        all_goals
          try rfl
          try
            intro a b hEq
            cases hEq⟩
  | mul hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "mul" [lhsIR, rhsIR]], by
        rw [CompilationModel.compileRequireFailCond, compileExpr_mul_ok hlhs hrhs]
        all_goals
          try rfl
          try
            intro a b hEq
            cases hEq⟩
  | div hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "div" [lhsIR, rhsIR]], by
        rw [CompilationModel.compileRequireFailCond, compileExpr_div_ok hlhs hrhs]
        all_goals
          try rfl
          try
            intro a b hEq
            cases hEq⟩
  | mod hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "mod" [lhsIR, rhsIR]], by
        rw [CompilationModel.compileRequireFailCond, compileExpr_mod_ok hlhs hrhs]
        all_goals
          try rfl
          try
            intro a b hEq
            cases hEq⟩
  | eq hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "eq" [lhsIR, rhsIR]], by
        rw [CompilationModel.compileRequireFailCond, compileExpr_eq_ok hlhs hrhs]
        all_goals
          try rfl
          try
            intro a b hEq
            cases hEq⟩
  | lt hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "lt" [lhsIR, rhsIR]], by
        rw [CompilationModel.compileRequireFailCond, compileExpr_lt_ok hlhs hrhs]
        all_goals
          try rfl
          try
            intro a b hEq
            cases hEq⟩
  | gt hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "gt" [lhsIR, rhsIR]], by
        rw [CompilationModel.compileRequireFailCond, compileExpr_gt_ok hlhs hrhs]
        all_goals
          try rfl
          try
            intro a b hEq
            cases hEq⟩
  | ge hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "lt" [lhsIR, rhsIR], by
        rw [CompilationModel.compileRequireFailCond, hlhs, hrhs]
        rfl⟩
  | le hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "gt" [lhsIR, rhsIR], by
        rw [CompilationModel.compileRequireFailCond, hlhs, hrhs]
        rfl⟩
  | logicalNot h =>
      rename_i expr
      rcases compileExpr_core_ok (fields := fields) h with ⟨exprIR, hexpr⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "iszero" [exprIR]], by
        rw [CompilationModel.compileRequireFailCond, compileExpr_logicalNot_ok hexpr]
        all_goals
          try rfl
          try
            intro a b hEq
            cases hEq⟩
  | logicalAnd hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero"
          [YulExpr.call "and" [CompilationModel.yulToBool lhsIR, CompilationModel.yulToBool rhsIR]], by
        rw [CompilationModel.compileRequireFailCond, compileExpr_logicalAnd_ok hlhs hrhs]
        all_goals
          try rfl
          try
            intro a b hEq
            cases hEq⟩
  | logicalOr hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero"
          [YulExpr.call "or" [CompilationModel.yulToBool lhsIR, CompilationModel.yulToBool rhsIR]], by
        rw [CompilationModel.compileRequireFailCond, compileExpr_logicalOr_ok hlhs hrhs]
        all_goals
          try rfl
          try
            intro a b hEq
            cases hEq⟩

 theorem eval_compileRequireFailCond_core_onExpr
     {fields : List Field}
     {runtime : SourceSemantics.RuntimeState}
     {state : IRState}
     {cond : Expr}
     (hcore : ExprCompileCore cond)
     (hexact : bindingsExactlyMatchIRVarsOnExpr cond runtime.bindings state)
     (hbounded : bindingsBounded runtime.bindings)
     (hpresent : exprBoundNamesPresent cond runtime.bindings)
     (hruntime : runtimeStateMatchesIR fields runtime state) :
     ∃ failCond,
       CompilationModel.compileRequireFailCond fields .calldata cond = Except.ok failCond ∧
       evalIRExpr state failCond =
         some (SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime cond = 0)) := by

   let finishIszeroEval {expr : Expr} (h : ExprCompileCore expr)
       (hexactExpr : bindingsExactlyMatchIRVarsOnExpr expr runtime.bindings state)
       (hpresentExpr : exprBoundNamesPresent expr runtime.bindings)
       {exprIR : YulExpr}
       (hexpr : CompilationModel.compileExpr fields .calldata expr = Except.ok exprIR) :
       evalIRExpr state (YulExpr.call "iszero" [exprIR]) =
         some (SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime expr = 0)) := by
     have heval := eval_compileExpr_core_onExpr h hexactExpr hbounded hpresentExpr hruntime
     rw [hexpr] at heval
     have hlt := evalExpr_lt_evmModulus_core_onExpr h hexactExpr hbounded hpresentExpr hruntime
     simpa [hexpr] using evalIRExpr_iszero_of_lt heval hlt
   cases hcore with
   | literal value =>
       rcases compileExpr_core_ok (fields := fields)
           (show ExprCompileCore (.literal value) from ExprCompileCore.literal value) with ⟨exprIR, hexpr⟩
       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
       · simp [CompilationModel.compileRequireFailCond, hexpr]
       · simpa using finishIszeroEval (expr := .literal value)
           (show ExprCompileCore (.literal value) from ExprCompileCore.literal value) hexact hpresent hexpr
   | param name =>
       rcases compileExpr_core_ok (fields := fields)
           (show ExprCompileCore (.param name) from ExprCompileCore.param name) with ⟨exprIR, hexpr⟩
       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
       · simp [CompilationModel.compileRequireFailCond, hexpr]
       · simpa using finishIszeroEval (expr := .param name)
           (show ExprCompileCore (.param name) from ExprCompileCore.param name) hexact hpresent hexpr
   | localVar name =>
       rcases compileExpr_core_ok (fields := fields)
           (show ExprCompileCore (.localVar name) from ExprCompileCore.localVar name) with ⟨exprIR, hexpr⟩
       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
       · simp [CompilationModel.compileRequireFailCond, hexpr]
       · simpa using finishIszeroEval (expr := .localVar name)
           (show ExprCompileCore (.localVar name) from ExprCompileCore.localVar name) hexact hpresent hexpr
   | caller =>
       rcases compileExpr_core_ok (fields := fields)
           (show ExprCompileCore (.caller) from ExprCompileCore.caller) with ⟨exprIR, hexpr⟩
       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
       · simp [CompilationModel.compileRequireFailCond, hexpr]
       · simpa using finishIszeroEval (expr := .caller)
           (show ExprCompileCore (.caller) from ExprCompileCore.caller) hexact hpresent hexpr
   | contractAddress =>
       rcases compileExpr_core_ok (fields := fields)
           (show ExprCompileCore (.contractAddress) from ExprCompileCore.contractAddress) with ⟨exprIR, hexpr⟩
       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
       · simp [CompilationModel.compileRequireFailCond, hexpr]
       · simpa using finishIszeroEval (expr := .contractAddress)
           (show ExprCompileCore (.contractAddress) from ExprCompileCore.contractAddress) hexact hpresent hexpr
   | msgValue =>
       rcases compileExpr_core_ok (fields := fields)
           (show ExprCompileCore (.msgValue) from ExprCompileCore.msgValue) with ⟨exprIR, hexpr⟩
       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
       · simp [CompilationModel.compileRequireFailCond, hexpr]
       · simpa using finishIszeroEval (expr := .msgValue)
           (show ExprCompileCore (.msgValue) from ExprCompileCore.msgValue) hexact hpresent hexpr
   | blockTimestamp =>
       rcases compileExpr_core_ok (fields := fields)
           (show ExprCompileCore (.blockTimestamp) from ExprCompileCore.blockTimestamp) with ⟨exprIR, hexpr⟩
       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
       · simp [CompilationModel.compileRequireFailCond, hexpr]
       · simpa using finishIszeroEval (expr := .blockTimestamp)
           (show ExprCompileCore (.blockTimestamp) from ExprCompileCore.blockTimestamp) hexact hpresent hexpr
   | blockNumber =>
       rcases compileExpr_core_ok (fields := fields)
           (show ExprCompileCore (.blockNumber) from ExprCompileCore.blockNumber) with ⟨exprIR, hexpr⟩
       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
       · simp [CompilationModel.compileRequireFailCond, hexpr]
       · simpa using finishIszeroEval (expr := .blockNumber)
           (show ExprCompileCore (.blockNumber) from ExprCompileCore.blockNumber) hexact hpresent hexpr
   | chainid =>
       rcases compileExpr_core_ok (fields := fields)
           (show ExprCompileCore (.chainid) from ExprCompileCore.chainid) with ⟨exprIR, hexpr⟩
       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
       · simp [CompilationModel.compileRequireFailCond, hexpr]
       · simpa using finishIszeroEval (expr := .chainid)
           (show ExprCompileCore (.chainid) from ExprCompileCore.chainid) hexact hpresent hexpr
   | add hL hR =>
       rename_i lhs rhs
       rcases compileExpr_core_ok (fields := fields)
           (show ExprCompileCore (.add lhs rhs) from ExprCompileCore.add hL hR) with ⟨exprIR, hexpr⟩
       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
       · simp [CompilationModel.compileRequireFailCond, hexpr]
       · simpa using finishIszeroEval (expr := .add lhs rhs)
           (show ExprCompileCore (.add lhs rhs) from ExprCompileCore.add hL hR) hexact hpresent hexpr
   | sub hL hR =>
       rename_i lhs rhs
       rcases compileExpr_core_ok (fields := fields)
           (show ExprCompileCore (.sub lhs rhs) from ExprCompileCore.sub hL hR) with ⟨exprIR, hexpr⟩
       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
       · simp [CompilationModel.compileRequireFailCond, hexpr]
       · simpa using finishIszeroEval (expr := .sub lhs rhs)
           (show ExprCompileCore (.sub lhs rhs) from ExprCompileCore.sub hL hR) hexact hpresent hexpr
   | mul hL hR =>
       rename_i lhs rhs
       rcases compileExpr_core_ok (fields := fields)
           (show ExprCompileCore (.mul lhs rhs) from ExprCompileCore.mul hL hR) with ⟨exprIR, hexpr⟩
       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
       · simp [CompilationModel.compileRequireFailCond, hexpr]
       · simpa using finishIszeroEval (expr := .mul lhs rhs)
           (show ExprCompileCore (.mul lhs rhs) from ExprCompileCore.mul hL hR) hexact hpresent hexpr
   | div hL hR =>
       rename_i lhs rhs
       rcases compileExpr_core_ok (fields := fields)
           (show ExprCompileCore (.div lhs rhs) from ExprCompileCore.div hL hR) with ⟨exprIR, hexpr⟩
       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
       · simp [CompilationModel.compileRequireFailCond, hexpr]
       · simpa using finishIszeroEval (expr := .div lhs rhs)
           (show ExprCompileCore (.div lhs rhs) from ExprCompileCore.div hL hR) hexact hpresent hexpr
   | mod hL hR =>
       rename_i lhs rhs
       rcases compileExpr_core_ok (fields := fields)
           (show ExprCompileCore (.mod lhs rhs) from ExprCompileCore.mod hL hR) with ⟨exprIR, hexpr⟩
       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
       · simp [CompilationModel.compileRequireFailCond, hexpr]
       · simpa using finishIszeroEval (expr := .mod lhs rhs)
           (show ExprCompileCore (.mod lhs rhs) from ExprCompileCore.mod hL hR) hexact hpresent hexpr
   | eq hL hR =>
       rename_i lhs rhs
       rcases compileExpr_core_ok (fields := fields)
           (show ExprCompileCore (.eq lhs rhs) from ExprCompileCore.eq hL hR) with ⟨exprIR, hexpr⟩
       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
       · simp [CompilationModel.compileRequireFailCond, hexpr]
       · simpa using finishIszeroEval (expr := .eq lhs rhs)
           (show ExprCompileCore (.eq lhs rhs) from ExprCompileCore.eq hL hR) hexact hpresent hexpr
   | lt hL hR =>
       rename_i lhs rhs
       rcases compileExpr_core_ok (fields := fields)
           (show ExprCompileCore (.lt lhs rhs) from ExprCompileCore.lt hL hR) with ⟨exprIR, hexpr⟩
       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
       · simp [CompilationModel.compileRequireFailCond, hexpr]
       · simpa using finishIszeroEval (expr := .lt lhs rhs)
           (show ExprCompileCore (.lt lhs rhs) from ExprCompileCore.lt hL hR) hexact hpresent hexpr
   | gt hL hR =>
       rename_i lhs rhs
       rcases compileExpr_core_ok (fields := fields)
           (show ExprCompileCore (.gt lhs rhs) from ExprCompileCore.gt hL hR) with ⟨exprIR, hexpr⟩
       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
       · simp [CompilationModel.compileRequireFailCond, hexpr]
       · simpa using finishIszeroEval (expr := .gt lhs rhs)
           (show ExprCompileCore (.gt lhs rhs) from ExprCompileCore.gt hL hR) hexact hpresent hexpr
   | ge hL hR =>
       rename_i lhs rhs
       rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
       rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
       have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
         bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
           intro name hname
           simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hname))
       have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
         bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
           intro name hname
           simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hname))
       have hpresentL : exprBoundNamesPresent lhs runtime.bindings :=
         exprBoundNamesPresent_of_subset hpresent (by
           intro name hname
           simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hname))
       have hpresentR : exprBoundNamesPresent rhs runtime.bindings :=
         exprBoundNamesPresent_of_subset hpresent (by
           intro name hname
           simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hname))
       have hlhsEval := eval_compileExpr_core_onExpr hL hexactL hbounded hpresentL hruntime
       have hrhsEval := eval_compileExpr_core_onExpr hR hexactR hbounded hpresentR hruntime
       rw [hlhs] at hlhsEval
       rw [hrhs] at hrhsEval
       have hlhsLt := evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime
       have hrhsLt := evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime
       refine ⟨YulExpr.call "lt" [lhsIR, rhsIR], ?_, ?_⟩
       · rw [CompilationModel.compileRequireFailCond, hlhs, hrhs]
         rfl
       · have hltEval :
             evalIRExpr state (YulExpr.call "lt" [lhsIR, rhsIR]) =
               some (SourceSemantics.boolWord
                 (SourceSemantics.evalExpr fields runtime lhs % Compiler.Constants.evmModulus <
                   SourceSemantics.evalExpr fields runtime rhs % Compiler.Constants.evmModulus)) := by
           simpa using evalIRExpr_lt_of_eval hlhsEval hrhsEval
         rw [show SourceSemantics.evalExpr fields runtime (.ge lhs rhs) =
             SourceSemantics.boolWord (decide (SourceSemantics.evalExpr fields runtime rhs ≤
               SourceSemantics.evalExpr fields runtime lhs)) by rfl]
         by_cases hlt : SourceSemantics.evalExpr fields runtime lhs < SourceSemantics.evalExpr fields runtime rhs
         · have hnotge : ¬ (SourceSemantics.evalExpr fields runtime rhs ≤
             SourceSemantics.evalExpr fields runtime lhs) := Nat.not_le_of_gt hlt
           simp [hltEval, Nat.mod_eq_of_lt hlhsLt, Nat.mod_eq_of_lt hrhsLt, hlt, hnotge,
             SourceSemantics.boolWord]
         · have hge : SourceSemantics.evalExpr fields runtime rhs ≤
             SourceSemantics.evalExpr fields runtime lhs := Nat.le_of_not_gt hlt
           simp [hltEval, Nat.mod_eq_of_lt hlhsLt, Nat.mod_eq_of_lt hrhsLt, hlt, hge,
             SourceSemantics.boolWord]
   | le hL hR =>
       rename_i lhs rhs
       rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
       rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
       have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
         bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
           intro name hname
           simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hname))
       have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
         bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
           intro name hname
           simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hname))
       have hpresentL : exprBoundNamesPresent lhs runtime.bindings :=
         exprBoundNamesPresent_of_subset hpresent (by
           intro name hname
           simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hname))
       have hpresentR : exprBoundNamesPresent rhs runtime.bindings :=
         exprBoundNamesPresent_of_subset hpresent (by
           intro name hname
           simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hname))
       have hlhsEval := eval_compileExpr_core_onExpr hL hexactL hbounded hpresentL hruntime
       have hrhsEval := eval_compileExpr_core_onExpr hR hexactR hbounded hpresentR hruntime
       rw [hlhs] at hlhsEval
       rw [hrhs] at hrhsEval
       have hlhsLt := evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime
       have hrhsLt := evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime
       refine ⟨YulExpr.call "gt" [lhsIR, rhsIR], ?_, ?_⟩
       · rw [CompilationModel.compileRequireFailCond, hlhs, hrhs]
         rfl
       · have hgtEval :
             evalIRExpr state (YulExpr.call "gt" [lhsIR, rhsIR]) =
               some (SourceSemantics.boolWord
                 (SourceSemantics.evalExpr fields runtime rhs % Compiler.Constants.evmModulus <
                   SourceSemantics.evalExpr fields runtime lhs % Compiler.Constants.evmModulus)) := by
           simpa using evalIRExpr_gt_of_eval hlhsEval hrhsEval
         rw [show SourceSemantics.evalExpr fields runtime (.le lhs rhs) =
             SourceSemantics.boolWord (decide (SourceSemantics.evalExpr fields runtime lhs ≤
               SourceSemantics.evalExpr fields runtime rhs)) by rfl]
         by_cases hgt : SourceSemantics.evalExpr fields runtime rhs < SourceSemantics.evalExpr fields runtime lhs
         · have hnotle : ¬ (SourceSemantics.evalExpr fields runtime lhs ≤
             SourceSemantics.evalExpr fields runtime rhs) := Nat.not_le_of_gt hgt
           simp [hgtEval, Nat.mod_eq_of_lt hlhsLt, Nat.mod_eq_of_lt hrhsLt, hgt, hnotle,
             SourceSemantics.boolWord]
         · have hle : SourceSemantics.evalExpr fields runtime lhs ≤
             SourceSemantics.evalExpr fields runtime rhs := Nat.le_of_not_gt hgt
           simp [hgtEval, Nat.mod_eq_of_lt hlhsLt, Nat.mod_eq_of_lt hrhsLt, hgt, hle,
             SourceSemantics.boolWord]
   | logicalNot h =>
       rename_i expr
       rcases compileExpr_core_ok (fields := fields)
           (show ExprCompileCore (.logicalNot expr) from ExprCompileCore.logicalNot h) with ⟨exprIR, hexpr⟩
       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
       · simp [CompilationModel.compileRequireFailCond, hexpr]
       · simpa using finishIszeroEval (expr := .logicalNot expr)
           (show ExprCompileCore (.logicalNot expr) from ExprCompileCore.logicalNot h) hexact hpresent hexpr
   | logicalAnd hL hR =>
       rename_i lhs rhs
       rcases compileExpr_core_ok (fields := fields)
           (show ExprCompileCore (.logicalAnd lhs rhs) from ExprCompileCore.logicalAnd hL hR) with ⟨exprIR, hexpr⟩
       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
       · simp [CompilationModel.compileRequireFailCond, hexpr]
       · simpa using finishIszeroEval (expr := .logicalAnd lhs rhs)
           (show ExprCompileCore (.logicalAnd lhs rhs) from ExprCompileCore.logicalAnd hL hR) hexact hpresent hexpr
   | logicalOr hL hR =>
       rename_i lhs rhs
       rcases compileExpr_core_ok (fields := fields)
           (show ExprCompileCore (.logicalOr lhs rhs) from ExprCompileCore.logicalOr hL hR) with ⟨exprIR, hexpr⟩
       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
       · simp [CompilationModel.compileRequireFailCond, hexpr]
       · simpa using finishIszeroEval (expr := .logicalOr lhs rhs)
           (show ExprCompileCore (.logicalOr lhs rhs) from ExprCompileCore.logicalOr hL hR) hexact hpresent hexpr

 theorem eval_compileRequireFailCond_core
     {fields : List Field}
     {runtime : SourceSemantics.RuntimeState}
     {state : IRState}
     {cond : Expr}
     (hcore : ExprCompileCore cond)
     (hexact : bindingsExactlyMatchIRVars runtime.bindings state)
     (hbounded : bindingsBounded runtime.bindings)
     (hpresent : exprBoundNamesPresent cond runtime.bindings)
     (hruntime : runtimeStateMatchesIR fields runtime state) :
     ∃ failCond,
       CompilationModel.compileRequireFailCond fields .calldata cond = Except.ok failCond ∧
       evalIRExpr state failCond =
         some (SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime cond = 0)) := by


theorem runtimeStateMatchesIR_setVar_bindValue
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state)
    (boundName : String)
    (value : Nat) :
    runtimeStateMatchesIR fields
      { runtime with bindings := SourceSemantics.bindValue runtime.bindings boundName value }
      (state.setVar boundName value) := by
  cases runtime
  cases state
  simpa [runtimeStateMatchesIR, IRState.setVar]

theorem runtimeStateMatchesIR_setVar_irrelevant
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {name : String}
    {value : Nat}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    runtimeStateMatchesIR fields runtime (state.setVar name value) := by
  cases state
  simpa [runtimeStateMatchesIR, IRState.setVar] using hmatch

def stmtResultMatchesIRExecExact :
    SourceSemantics.StmtResult → IRExecResult → Prop
  | .continue runtime, .continue state =>
      bindingsExactlyMatchIRVars runtime.bindings state ∧
      bindingsBounded runtime.bindings
  | .stop runtime, .stop state =>
      bindingsExactlyMatchIRVars runtime.bindings state ∧
      bindingsBounded runtime.bindings
  | .return _ runtime, .return _ state =>
      bindingsExactlyMatchIRVars runtime.bindings state ∧
      bindingsBounded runtime.bindings
  | .revert, .revert _ => True
  | _, _ => False

/-- Statement fragment whose correctness can already be discharged using the
expression core, without storage, calls, or ABI encoding. -/
inductive StmtCompileCore : Stmt → Prop where
  | letVar {name : String} {value : Expr} :
      ExprCompileCore value → StmtCompileCore (.letVar name value)
  | assignVar {name : String} {value : Expr} :
      ExprCompileCore value → StmtCompileCore (.assignVar name value)
  | require_ {cond : Expr} {message : String} :
      ExprCompileCore cond → StmtCompileCore (.require cond message)
  | return_ {value : Expr} :
      ExprCompileCore value → StmtCompileCore (.return value)
  | stop :
      StmtCompileCore .stop

theorem compileStmt_core_ok
    {fields : List Field}
    {stmt : Stmt}
    (hcore : StmtCompileCore stmt) :
    ∃ bodyIR, CompilationModel.compileStmt fields [] [] .calldata [] false [] stmt = Except.ok bodyIR := by
  cases hcore with
  | letVar hvalue =>
      rename_i name value
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      exact ⟨[YulStmt.let_ name valueIR], by
        rw [CompilationModel.compileStmt, hvalueIR]
        rfl⟩
  | assignVar hvalue =>
      rename_i name value
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      exact ⟨[YulStmt.assign name valueIR], by
        rw [CompilationModel.compileStmt, hvalueIR]
        rfl⟩
  | require_ hcond =>
      rename_i cond message
      rcases compileRequireFailCond_core_ok hcond with ⟨failCond, hfailCond⟩
      exact ⟨[YulStmt.if_ failCond (CompilationModel.revertWithMessage message)], by
        rw [CompilationModel.compileStmt, hfailCond]
        rfl⟩
  | return_ hvalue =>
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      exact ⟨[ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
            , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ], by
        rw [CompilationModel.compileStmt, hvalueIR]
        rfl⟩
  | stop =>
      exact ⟨[YulStmt.expr (YulExpr.call "stop" [])], by
        rw [CompilationModel.compileStmt]
        rfl⟩

theorem runtimeStateMatchesIR_setMemory
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state)
    (offset value : Nat) :
    runtimeStateMatchesIR fields runtime
      { state with memory := fun o => if o = offset then value else state.memory o } := by
  cases runtime
  cases state
  simpa [runtimeStateMatchesIR]

theorem runtimeStateMatchesIR_setTransientStorage
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state)
    (offset value : Nat) :
    runtimeStateMatchesIR fields
      { runtime with
          world := {
            runtime.world with
            transientStorage := fun o => if o = offset then value else runtime.world.transientStorage o
          } }
      { state with
          transientStorage := fun o => if o = offset then value else state.transientStorage o } := by
   cases runtime
   cases state
   simpa [runtimeStateMatchesIR]

theorem bindingsExactlyMatchIRVars_setMemory
    {bindings : List (String × Nat)}
    {state : IRState}
    (hexact : bindingsExactlyMatchIRVars bindings state)
    (offset value : Nat) :
    bindingsExactlyMatchIRVars bindings
      { state with memory := fun o => if o = offset then value else state.memory o } := by
  intro name
  simpa [IRState.getVar] using hexact name

theorem bindingsExactlyMatchIRVarsOnScope_setMemory
    {scope : List String}
    {bindings : List (String × Nat)}
    {state : IRState}
    (hexact : bindingsExactlyMatchIRVarsOnScope scope bindings state)
    (offset value : Nat) :
    bindingsExactlyMatchIRVarsOnScope scope bindings
      { state with memory := fun o => if o = offset then value else state.memory o } := by
  intro name hname
  simpa [IRState.getVar] using hexact name hname

theorem bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant
    {scope : List String}
    {bindings : List (String × Nat)}
    {state : IRState}
    {tempName : String}
    {value : Nat}
    (hexact : bindingsExactlyMatchIRVarsOnScope scope bindings state)
    (hfresh : tempName ∉ scope) :
    bindingsExactlyMatchIRVarsOnScope scope bindings (state.setVar tempName value) := by
  intro name hname
  by_cases hEq : name = tempName
  · subst hEq
    exact False.elim (hfresh hname)
  · rw [getVar_setVar_ne state tempName name value hEq]
    exact hexact name hname

theorem bindingsExactlyMatchIRVarsOnScope_setVar_bindValue
    {scope : List String}
    {bindings : List (String × Nat)}
    {state : IRState}
    {boundName : String}
    {value : Nat}
    (hexact : bindingsExactlyMatchIRVarsOnScope scope bindings state) :
    bindingsExactlyMatchIRVarsOnScope (boundName :: scope)
      (SourceSemantics.bindValue bindings boundName value)
      (state.setVar boundName value) := by
  intro name hname
  simp at hname
  rcases hname with rfl | hname
  · simp [lookupBinding?_bindValue_eq]
  · by_cases hEq : name = boundName
    · subst hEq
      simp [lookupBinding?_bindValue_eq]
    · rw [lookupBinding?_bindValue_ne bindings boundName name value hEq]
      rw [getVar_setVar_ne state boundName name value hEq]
      exact hexact name hname

@[simp] theorem encodeEvents_withTransactionContext
    (world : Verity.ContractState) (tx : IRTransaction) :
    SourceSemantics.encodeEvents (SourceSemantics.withTransactionContext world tx).events =
      SourceSemantics.encodeEvents world.events := by
  rfl

@[simp] theorem encodeStorage_withTransactionContext
    (spec : CompilationModel)
    (world : Verity.ContractState)
    (tx : IRTransaction) :
    SourceSemantics.encodeStorage spec (SourceSemantics.withTransactionContext world tx) =
      SourceSemantics.encodeStorage spec world := by
   funext slot
   simp [SourceSemantics.encodeStorage, SourceSemantics.withTransactionContext,
     SourceSemantics.encodeStorageAt]

def stmtResultMatchesIRExec
    (fields : List Field) :
    SourceSemantics.StmtResult → IRExecResult → Prop
  | .continue runtime, .continue state => runtimeStateMatchesIR fields runtime state
  | .stop runtime, .stop state => runtimeStateMatchesIR fields runtime state
  | .return value runtime, .return value' state =>
      value = value' ∧ runtimeStateMatchesIR fields runtime state
  | .revert, .revert _ => True
  | _, _ => False

def stmtResultToSourceResult
    (spec : CompilationModel)
    (initialWorld : Verity.ContractState) :
    SourceSemantics.StmtResult → SourceSemantics.SourceContractResult
  | .continue runtime => SourceSemantics.successResult spec runtime.world none
  | .stop runtime => SourceSemantics.successResult spec runtime.world none
  | .return value runtime => SourceSemantics.successResult spec runtime.world (some value)
  | .revert => SourceSemantics.revertedResult spec initialWorld

def sourceResultMatchesIRResult
    (source : SourceSemantics.SourceContractResult)
    (ir : IRResult) : Prop :=
  source.success = ir.success ∧
  source.returnValue = ir.returnValue ∧
  source.finalStorage = ir.finalStorage ∧
  source.events = ir.events

theorem exec_compileStmt_letVar_core
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {name : String}
    {value : Expr}
    (hcore : ExprCompileCore value)
    (hexact : bindingsExactlyMatchIRVars runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hpresent : exprBoundNamesPresent value runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmt fields [] [] .calldata [] false [] (.letVar name value) = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmt fields runtime (.letVar name value)
      let irExec := execIRStmts (bodyIR.length + 1) state bodyIR
      stmtResultMatchesIRExec fields sourceResult irExec ∧
      stmtResultMatchesIRExecExact sourceResult irExec := by
   rcases compileExpr_core_ok hcore with ⟨valueIR, hvalueIR⟩
   refine ⟨[YulStmt.let_ name valueIR], ?_, ?_⟩
   · rw [CompilationModel.compileStmt, hvalueIR]
     rfl
   · let valueNat := SourceSemantics.evalExpr fields runtime value
     have heval := eval_compileExpr_core hcore hexact hbounded hpresent hruntime
     rw [hvalueIR] at heval
     have heval' : evalIRExpr state valueIR = some valueNat := by
       simpa [valueNat] using heval
     have hvalueLt := evalExpr_lt_evmModulus_core hcore hexact hbounded hpresent hruntime
     have hruntime' :
         runtimeStateMatchesIR fields
           ({ runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat })
           (state.setVar name valueNat) :=
       runtimeStateMatchesIR_setVar_bindValue hruntime name valueNat
     have hexact' :
         bindingsExactlyMatchIRVars
           (SourceSemantics.bindValue runtime.bindings name valueNat)
           (state.setVar name valueNat) :=
       bindingsExactlyMatchIRVars_setVar_bindValue hexact name valueNat
     have hbounded' :
         bindingsBounded (SourceSemantics.bindValue runtime.bindings name valueNat) :=
       bindingsBounded_bindValue hbounded name valueNat hvalueLt
     have hirExec :
         execIRStmts ([YulStmt.let_ name valueIR].length + 1) state [YulStmt.let_ name valueIR] =
           .continue (state.setVar name valueNat) := by
       simp [execIRStmts, execIRStmt, heval', valueNat]
     constructor
     · rw [SourceSemantics.execStmt, hirExec]
       exact hruntime'
     · rw [SourceSemantics.execStmt, hirExec]
       exact ⟨hexact', hbounded'⟩

theorem exec_compileStmt_assignVar_core
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {name : String}
    {value : Expr}
    (hcore : ExprCompileCore value)
    (hexact : bindingsExactlyMatchIRVars runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hpresent : exprBoundNamesPresent value runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmt fields [] [] .calldata [] false [] (.assignVar name value) = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmt fields runtime (.assignVar name value)
      let irExec := execIRStmts (bodyIR.length + 1) state bodyIR
      stmtResultMatchesIRExec fields sourceResult irExec ∧
      stmtResultMatchesIRExecExact sourceResult irExec := by
   rcases compileExpr_core_ok hcore with ⟨valueIR, hvalueIR⟩
   refine ⟨[YulStmt.assign name valueIR], ?_, ?_⟩
   · rw [CompilationModel.compileStmt, hvalueIR]
     rfl
   · let valueNat := SourceSemantics.evalExpr fields runtime value
     have heval := eval_compileExpr_core hcore hexact hbounded hpresent hruntime
     rw [hvalueIR] at heval
     have heval' : evalIRExpr state valueIR = some valueNat := by
       simpa [valueNat] using heval
     have hvalueLt := evalExpr_lt_evmModulus_core hcore hexact hbounded hpresent hruntime
     have hruntime' :
         runtimeStateMatchesIR fields
           ({ runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat })
           (state.setVar name valueNat) :=
       runtimeStateMatchesIR_setVar_bindValue hruntime name valueNat
     have hexact' :
         bindingsExactlyMatchIRVars
           (SourceSemantics.bindValue runtime.bindings name valueNat)
           (state.setVar name valueNat) :=
       bindingsExactlyMatchIRVars_setVar_bindValue hexact name valueNat
     have hbounded' :
         bindingsBounded (SourceSemantics.bindValue runtime.bindings name valueNat) :=
       bindingsBounded_bindValue hbounded name valueNat hvalueLt
     have hirExec :
         execIRStmts ([YulStmt.assign name valueIR].length + 1) state [YulStmt.assign name valueIR] =
           .continue (state.setVar name valueNat) := by
       simp [execIRStmts, execIRStmt, heval', valueNat]
     constructor
     · rw [SourceSemantics.execStmt, hirExec]
       exact hruntime'
     · rw [SourceSemantics.execStmt, hirExec]
       exact ⟨hexact', hbounded'⟩

theorem exec_compileStmt_return_core
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {value : Expr}
    (hcore : ExprCompileCore value)
    (hexact : bindingsExactlyMatchIRVars runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hpresent : exprBoundNamesPresent value runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmt fields [] [] .calldata [] false [] (.return value) = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmt fields runtime (.return value)
      let irExec := execIRStmts (bodyIR.length + 1) state bodyIR
      stmtResultMatchesIRExec fields sourceResult irExec ∧
      stmtResultMatchesIRExecExact sourceResult irExec := by
   rcases compileExpr_core_ok hcore with ⟨valueIR, hvalueIR⟩
   let retVal := SourceSemantics.evalExpr fields runtime value
   let state' := { state with memory := fun o => if o = 0 then retVal else state.memory o }
   refine ⟨[ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
           , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ], ?_, ?_⟩
   · rw [CompilationModel.compileStmt, hvalueIR]
     rfl
   · have heval := eval_compileExpr_core hcore hexact hbounded hpresent hruntime
     rw [hvalueIR] at heval
     have heval' : evalIRExpr state valueIR = some retVal := by
       simpa [retVal] using heval
     have hruntime' : runtimeStateMatchesIR fields runtime state' :=
       runtimeStateMatchesIR_setMemory hruntime 0 retVal
     have hexact' : bindingsExactlyMatchIRVars runtime.bindings state' :=
       bindingsExactlyMatchIRVars_setMemory hexact 0 retVal
     have hmstore :
         execIRStmt 2 state (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])) =
           .continue state' := by
       simp [execIRStmt, evalIRExpr, heval', retVal, state']
     have hreturn :
         execIRStmt 1 state' (YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])) =
           .return retVal state' := by
       simp [execIRStmt, evalIRExpr, retVal, state']
     have hirExec :
         execIRStmts
             ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
              , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ].length + 1)
             state
             [ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
             , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] =
           .return retVal state' := by
       simp [execIRStmts, hmstore, hreturn]
     constructor
     · rw [SourceSemantics.execStmt, hirExec]
       exact ⟨rfl, hruntime'⟩
     · rw [SourceSemantics.execStmt, hirExec]
       exact ⟨hexact', hbounded⟩

theorem exec_compileStmt_return_core_extraFuel
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {value : Expr}
    (extraFuel : Nat)
    (hcore : ExprCompileCore value)
    (hexact : bindingsExactlyMatchIRVars runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hpresent : exprBoundNamesPresent value runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmt fields [] [] .calldata [] false [] (.return value) = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmt fields runtime (.return value)
      let irExec := execIRStmts (bodyIR.length + extraFuel + 1) state bodyIR
      stmtResultMatchesIRExec fields sourceResult irExec ∧
      stmtResultMatchesIRExecExact sourceResult irExec := by
   rcases compileExpr_core_ok hcore with ⟨valueIR, hvalueIR⟩
   let retVal := SourceSemantics.evalExpr fields runtime value
   let state' := { state with memory := fun o => if o = 0 then retVal else state.memory o }
   refine ⟨[ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
           , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ], ?_, ?_⟩
   · rw [CompilationModel.compileStmt, hvalueIR]
     rfl
   · have heval := eval_compileExpr_core hcore hexact hbounded hpresent hruntime
     rw [hvalueIR] at heval
     have heval' : evalIRExpr state valueIR = some retVal := by
       simpa [retVal] using heval
     have hruntime' : runtimeStateMatchesIR fields runtime state' :=
       runtimeStateMatchesIR_setMemory hruntime 0 retVal
     have hexact' : bindingsExactlyMatchIRVars runtime.bindings state' :=
       bindingsExactlyMatchIRVars_setMemory hexact 0 retVal
     have hmstore :
         execIRStmt (extraFuel + 2) state
           (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])) =
           .continue state' := by
       simp [execIRStmt, evalIRExpr, heval', retVal, state']
     have hreturn :
         execIRStmt (extraFuel + 1) state'
           (YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])) =
           .return retVal state' := by
       simp [execIRStmt, evalIRExpr, retVal, state']
     have hirExec :
         execIRStmts
             ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
              , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ].length +
               extraFuel + 1)
             state
             [ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
             , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] =
           .return retVal state' := by
       simp [execIRStmts, hmstore, hreturn, Nat.add_comm]
     constructor
     · rw [SourceSemantics.execStmt, hirExec]
       exact ⟨rfl, hruntime'⟩
     · rw [SourceSemantics.execStmt, hirExec]
       exact ⟨hexact', hbounded⟩

theorem exec_compileStmt_stop_core
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hexact : bindingsExactlyMatchIRVars runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmt fields [] [] .calldata [] false [] .stop = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmt fields runtime .stop
      let irExec := execIRStmts (bodyIR.length + 1) state bodyIR
      stmtResultMatchesIRExec fields sourceResult irExec ∧
      stmtResultMatchesIRExecExact sourceResult irExec := by
  refine ⟨[YulStmt.expr (YulExpr.call "stop" [])], ?_, ?_⟩
  · rw [CompilationModel.compileStmt]
    rfl
  · constructor
    · have hirExec :
          execIRStmts ([YulStmt.expr (YulExpr.call "stop" [])].length + 1) state
            [YulStmt.expr (YulExpr.call "stop" [])] = .stop state := by
        simp [execIRStmts]
      rw [SourceSemantics.execStmt, hirExec]
      exact hruntime
    · have hirExec :
          execIRStmts ([YulStmt.expr (YulExpr.call "stop" [])].length + 1) state
            [YulStmt.expr (YulExpr.call "stop" [])] = .stop state := by
        simp [execIRStmts]
      rw [SourceSemantics.execStmt, hirExec]
      exact ⟨hexact, hbounded⟩

theorem exec_compileStmt_stop_core_extraFuel
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (extraFuel : Nat)
    (hexact : bindingsExactlyMatchIRVars runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmt fields [] [] .calldata [] false [] .stop = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmt fields runtime .stop
      let irExec := execIRStmts (bodyIR.length + extraFuel + 1) state bodyIR
      stmtResultMatchesIRExec fields sourceResult irExec ∧
      stmtResultMatchesIRExecExact sourceResult irExec := by
  refine ⟨[YulStmt.expr (YulExpr.call "stop" [])], ?_, ?_⟩
  · rw [CompilationModel.compileStmt]
    rfl
  · have hirExec :
        execIRStmts
          ([YulStmt.expr (YulExpr.call "stop" [])].length + extraFuel + 1)
          state
          [YulStmt.expr (YulExpr.call "stop" [])] = .stop state := by
      simp [execIRStmts]
    constructor
    · rw [SourceSemantics.execStmt, hirExec]
      exact hruntime
    · rw [SourceSemantics.execStmt, hirExec]
      exact ⟨hexact, hbounded⟩

def scopeNamesPresent (scope : List String) (bindings : List (String × Nat)) : Prop :=
  ∀ name, name ∈ scope → ∃ value, lookupBinding? bindings name = some value

def scopeNamesIncluded
    (scope inScopeNames : List String) : Prop :=
  ∀ name, name ∈ scope → name ∈ inScopeNames

-- exprBoundNamesInScope is now in ExprCore.lean

theorem bindingsExactlyMatchIRVarsOnScope_implies_onExpr
    {scope : List String}
    {expr : Expr}
    {bindings : List (String × Nat)}
    {state : IRState}
    (hexact : bindingsExactlyMatchIRVarsOnScope scope bindings state)
    (hinScope : exprBoundNamesInScope expr scope) :
    bindingsExactlyMatchIRVarsOnExpr expr bindings state := by
  intro name hname
  exact hexact name (hinScope name hname)

theorem eval_compileExpr_core_of_scope
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope : List String}
    {expr : Expr}
    (hcore : ExprCompileCore expr)
    (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hinScope : exprBoundNamesInScope expr scope)
    (hbounded : bindingsBounded runtime.bindings)
    (hpresent : exprBoundNamesPresent expr runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata expr |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime expr) :=
  eval_compileExpr_core_onExpr hcore
    (bindingsExactlyMatchIRVarsOnScope_implies_onExpr hexact hinScope)
    hbounded hpresent hruntime

theorem evalExpr_lt_evmModulus_core_of_scope
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope : List String}
    {expr : Expr}
    (hcore : ExprCompileCore expr)
    (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hinScope : exprBoundNamesInScope expr scope)
    (hbounded : bindingsBounded runtime.bindings)
    (hpresent : exprBoundNamesPresent expr runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    SourceSemantics.evalExpr fields runtime expr < Compiler.Constants.evmModulus :=
  evalExpr_lt_evmModulus_core_onExpr hcore
    (bindingsExactlyMatchIRVarsOnScope_implies_onExpr hexact hinScope)
    hbounded hpresent hruntime

 theorem eval_compileRequireFailCond_core_of_scope
     {fields : List Field}
     {runtime : SourceSemantics.RuntimeState}
     {state : IRState}
     {scope : List String}
     {cond : Expr}
     (hcore : ExprCompileCore cond)
     (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
     (hinScope : exprBoundNamesInScope cond scope)
     (hbounded : bindingsBounded runtime.bindings)
     (hpresent : exprBoundNamesPresent cond runtime.bindings)
     (hruntime : runtimeStateMatchesIR fields runtime state) :
     ∃ failCond,
       CompilationModel.compileRequireFailCond fields .calldata cond = Except.ok failCond ∧
       evalIRExpr state failCond =
         some (SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime cond = 0)) := by


theorem bindingsExactlyMatchIRVarsOnScope_of_included
    {scope largerScope : List String}
    {bindings : List (String × Nat)}
    {state : IRState}
    (hexact : bindingsExactlyMatchIRVarsOnScope largerScope bindings state)
    (hincluded : scopeNamesIncluded scope largerScope) :
    bindingsExactlyMatchIRVarsOnScope scope bindings state := by
  intro name hname
  exact hexact name (hincluded name hname)

theorem exprBoundNamesPresent_of_scope
    {expr : Expr}
    {scope : List String}
    {bindings : List (String × Nat)}
    (hscope : scopeNamesPresent scope bindings)
    (hinScope : exprBoundNamesInScope expr scope) :
    exprBoundNamesPresent expr bindings := by
  intro name hname
  exact hscope name (hinScope name hname)

theorem scopeNamesPresent_of_included
    {scope largerScope : List String}
    {bindings : List (String × Nat)}
    (hscope : scopeNamesPresent largerScope bindings)
    (hincluded : scopeNamesIncluded scope largerScope) :
    scopeNamesPresent scope bindings := by
  intro name hname
  exact hscope name (hincluded name hname)

theorem scopeNamesPresent_bindValue
    {scope : List String}
    {bindings : List (String × Nat)}
    {boundName : String}
    {value : Nat}
    (hscope : scopeNamesPresent scope bindings) :
    scopeNamesPresent scope (SourceSemantics.bindValue bindings boundName value) := by
  intro name hmem
  rcases hscope name hmem with ⟨found, hfound⟩
  by_cases hEq : name = boundName
  · subst hEq
    exact ⟨value, lookupBinding?_bindValue_eq bindings name value⟩
  · exact ⟨found, by
      rw [lookupBinding?_bindValue_ne bindings boundName name value hEq, hfound]⟩

theorem scopeNamesPresent_cons_bindValue
    {scope : List String}
    {bindings : List (String × Nat)}
    {boundName : String}
    {value : Nat}
    (hscope : scopeNamesPresent scope bindings) :
    scopeNamesPresent (boundName :: scope) (SourceSemantics.bindValue bindings boundName value) := by
  intro name hmem
  simp at hmem
  rcases hmem with rfl | hmem
  · exact ⟨value, lookupBinding?_bindValue_eq bindings name value⟩
  · exact (scopeNamesPresent_bindValue hscope) name hmem

-- StmtListCompileCore and StmtListTerminalCore are now in ExprCore.lean

theorem stmtListTerminalCore_return_tail_compileCore
    {scope : List String}
    {value : Expr}
    {rest : List Stmt}
    (hterminal : StmtListTerminalCore scope (.return value :: rest)) :
    StmtListCompileCore scope rest := by
  cases hterminal with
  | return_ _ _ hrest =>
      exact hrest

theorem stmtListTerminalCore_stop_tail_compileCore
    {scope : List String}
    {rest : List Stmt}
    (hterminal : StmtListTerminalCore scope (.stop :: rest)) :
    StmtListCompileCore scope rest := by
  cases hterminal with
  | stop hrest =>
      exact hrest

theorem stmtListTerminalCore_ite_tail_compileCore
    {scope : List String}
    {cond : Expr}
    {thenBranch elseBranch rest : List Stmt}
    (hterminal : StmtListTerminalCore scope (.ite cond thenBranch elseBranch :: rest)) :
    StmtListCompileCore scope rest := by
  cases hterminal with
  | ite _ _ _ _ hrest =>
      exact hrest

theorem stmtListTerminalCore_ne_nil
    {scope : List String}
    {stmts : List Stmt}
    (hterminal : StmtListTerminalCore scope stmts) :
    stmts ≠ [] := by
  cases hterminal <;> simp

theorem compileStmt_core_ok_any_scope
    {fields : List Field}
    {inScopeNames : List String}
    {stmt : Stmt}
    (hcore : StmtCompileCore stmt) :
    ∃ bodyIR,
      CompilationModel.compileStmt
        fields [] [] .calldata [] false inScopeNames stmt = Except.ok bodyIR := by
  cases hcore with
  | letVar hvalue =>
      rename_i name value
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      exact ⟨[YulStmt.let_ name valueIR], by
        rw [CompilationModel.compileStmt, hvalueIR]
        rfl⟩
  | assignVar hvalue =>
      rename_i name value
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      exact ⟨[YulStmt.assign name valueIR], by
        rw [CompilationModel.compileStmt, hvalueIR]
        rfl⟩
  | require_ hcond =>
      rename_i cond message
      rcases compileRequireFailCond_core_ok hcond with ⟨failCond, hfailCond⟩
      exact ⟨[YulStmt.if_ failCond (CompilationModel.revertWithMessage message)], by
        rw [CompilationModel.compileStmt, hfailCond]
        rfl⟩
  | return_ hvalue =>
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      exact ⟨[ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
            , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ], by
        rw [CompilationModel.compileStmt, hvalueIR]
        rfl⟩
  | stop =>
      exact ⟨[YulStmt.expr (YulExpr.call "stop" [])], by
        rw [CompilationModel.compileStmt]
        rfl⟩

theorem compileStmtList_cons_ok_of_compileStmt_ok
    {fields : List Field}
    {inScopeNames : List String}
    {stmt : Stmt}
    {rest : List Stmt}
    {headIR tailIR : List YulStmt}
    (hhead :
      CompilationModel.compileStmt
        fields [] [] .calldata [] false inScopeNames stmt = Except.ok headIR)
    (htail :
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false
          (collectStmtNames stmt ++ inScopeNames) rest = Except.ok tailIR) :
    CompilationModel.compileStmtList
      fields [] [] .calldata [] false inScopeNames (stmt :: rest) =
        Except.ok (headIR ++ tailIR) := by
  rw [CompilationModel.compileStmtList, hhead]
  dsimp
  rw [htail]
  rfl

theorem compileStmtList_cons_ok_inv
    {fields : List Field}
    {inScopeNames : List String}
    {stmt : Stmt}
    {rest : List Stmt}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames (stmt :: rest) =
          Except.ok bodyIR) :
    ∃ headIR tailIR,
      CompilationModel.compileStmt
        fields [] [] .calldata [] false inScopeNames stmt = Except.ok headIR ∧
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false
          (collectStmtNames stmt ++ inScopeNames) rest = Except.ok tailIR ∧
      bodyIR = headIR ++ tailIR := by
  rw [CompilationModel.compileStmtList] at hcompile
  cases hhead : CompilationModel.compileStmt
      fields [] [] .calldata [] false inScopeNames stmt with
  | error err =>
      simp [hhead] at hcompile
      cases hcompile
  | ok headIR =>
      cases htail : CompilationModel.compileStmtList
          fields [] [] .calldata [] false
            (collectStmtNames stmt ++ inScopeNames) rest with
      | error err =>
          simp [hhead, htail] at hcompile
          cases hcompile
      | ok tailIR =>
          simp [hhead, htail] at hcompile
          injection hcompile with hbody
          subst hbody
          refine ⟨headIR, tailIR, ?_, ?_, rfl⟩
          · simpa [hhead]
          · simpa [htail]

theorem compileStmt_terminal_ite_ok_inv
    {fields : List Field}
    {inScopeNames : List String}
    {cond : Expr}
    {thenBranch elseBranch : List Stmt}
    {bodyIR : List YulStmt}
    (helseNonempty : elseBranch.isEmpty = false)
    (hcompile :
      CompilationModel.compileStmt
        fields [] [] .calldata [] false inScopeNames
          (.ite cond thenBranch elseBranch) = Except.ok bodyIR) :
    ∃ condIR thenIR elseIR tempName,
      CompilationModel.compileExpr fields .calldata cond = Except.ok condIR ∧
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames thenBranch = Except.ok thenIR ∧
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames elseBranch = Except.ok elseIR ∧
      tempName =
        CompilationModel.pickFreshName "__ite_cond"
          (inScopeNames ++ collectExprNames cond ++
            collectStmtListNames thenBranch ++ collectStmtListNames elseBranch) ∧
      bodyIR =
        [YulStmt.block
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]] := by
  unfold CompilationModel.compileStmt at hcompile
  cases hcond : CompilationModel.compileExpr fields .calldata cond with
  | error err =>
      simp [hcond] at hcompile
      cases hcompile
  | ok condIR =>
      cases hthen : CompilationModel.compileStmtList
          fields [] [] .calldata [] false inScopeNames thenBranch with
      | error err =>
          simp [hcond, hthen] at hcompile
          cases hcompile
      | ok thenIR =>
          cases helse : CompilationModel.compileStmtList
              fields [] [] .calldata [] false inScopeNames elseBranch with
          | error err =>
              simp [hcond, hthen, helse] at hcompile
              cases hcompile
          | ok elseIR =>
              simp [hcond, hthen, helse, helseNonempty] at hcompile
              refine ⟨condIR, thenIR, elseIR,
                CompilationModel.pickFreshName "__ite_cond"
                  (inScopeNames ++ collectExprNames cond ++
                    collectStmtListNames thenBranch ++ collectStmtListNames elseBranch),
                ?_, ?_, ?_, rfl, ?_⟩
              · simpa [hcond]
              · simpa [hthen]
              · simpa [helse]
              · injection hcompile with hbody
                simpa [List.append_assoc] using hbody.symm

theorem compileStmtList_terminal_ite_ok_inv
    {fields : List Field}
    {inScopeNames : List String}
    {cond : Expr}
    {thenBranch elseBranch rest : List Stmt}
    {bodyIR : List YulStmt}
    (helseNonempty : elseBranch.isEmpty = false)
    (hcompile :
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames
          (.ite cond thenBranch elseBranch :: rest) = Except.ok bodyIR) :
    ∃ condIR thenIR elseIR tailIR tempName,
      CompilationModel.compileExpr fields .calldata cond = Except.ok condIR ∧
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames thenBranch = Except.ok thenIR ∧
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames elseBranch = Except.ok elseIR ∧
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false
          (collectStmtNames (.ite cond thenBranch elseBranch) ++ inScopeNames) rest =
          Except.ok tailIR ∧
      tempName =
        CompilationModel.pickFreshName "__ite_cond"
          (inScopeNames ++ collectExprNames cond ++
            collectStmtListNames thenBranch ++ collectStmtListNames elseBranch) ∧
      bodyIR =
        [YulStmt.block
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]] ++
          tailIR := by
  rcases compileStmtList_cons_ok_inv
      (fields := fields)
      (inScopeNames := inScopeNames)
      (stmt := .ite cond thenBranch elseBranch)
      (rest := rest)
      hcompile with
    ⟨headIR, tailIR, hhead, htail, hbody⟩
  rcases compileStmt_terminal_ite_ok_inv
      (fields := fields)
      (inScopeNames := inScopeNames)
      (cond := cond)
      (thenBranch := thenBranch)
      (elseBranch := elseBranch)
      (bodyIR := headIR)
      helseNonempty
      hhead with
    ⟨condIR, thenIR, elseIR, tempName, hcond, hthen, helse, htemp, hheadIR⟩
  refine ⟨condIR, thenIR, elseIR, tailIR, tempName, hcond, hthen, helse, htail, htemp, ?_⟩
  simpa [hheadIR] using hbody

theorem compileStmtList_core_ok
    {fields : List Field}
    {scope inScopeNames : List String}
    {stmts : List Stmt}
    (hcore : StmtListCompileCore scope stmts) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames stmts = Except.ok bodyIR := by
  induction hcore generalizing inScopeNames
  case nil =>
      exact ⟨[], rfl⟩
  case letVar scope name value rest hvalue _ hrest ih =>
      rcases compileStmt_core_ok_any_scope (fields := fields) (inScopeNames := inScopeNames)
        (stmt := .letVar name value) (.letVar hvalue) with ⟨headIR, hheadIR⟩
      rcases ih (inScopeNames := collectStmtNames (.letVar name value) ++ inScopeNames) with
        ⟨tailIR, htailIR⟩
      refine ⟨headIR ++ tailIR, ?_⟩
      rw [CompilationModel.compileStmtList, hheadIR]
      dsimp
      rw [htailIR]
      rfl
  case assignVar scope name value rest hvalue _ hrest ih =>
      rcases compileStmt_core_ok_any_scope (fields := fields) (inScopeNames := inScopeNames)
        (stmt := .assignVar name value) (.assignVar hvalue) with ⟨headIR, hheadIR⟩
      rcases ih (inScopeNames := collectStmtNames (.assignVar name value) ++ inScopeNames) with
        ⟨tailIR, htailIR⟩
      refine ⟨headIR ++ tailIR, ?_⟩
      rw [CompilationModel.compileStmtList, hheadIR]
      dsimp
      rw [htailIR]
      rfl
  case require_ scope cond message rest hcond _ hrest ih =>
      rcases compileStmt_core_ok_any_scope (fields := fields) (inScopeNames := inScopeNames)
        (stmt := .require cond message) (.require_ hcond) with ⟨headIR, hheadIR⟩
      rcases ih (inScopeNames := collectStmtNames (.require cond message) ++ inScopeNames) with
        ⟨tailIR, htailIR⟩
      refine ⟨headIR ++ tailIR, ?_⟩
      rw [CompilationModel.compileStmtList, hheadIR]
      dsimp
      rw [htailIR]
      rfl
  case return_ scope value rest hvalue _ hrest ih =>
      rcases compileStmt_core_ok_any_scope (fields := fields) (inScopeNames := inScopeNames)
        (stmt := .return value) (.return_ hvalue) with ⟨headIR, hheadIR⟩
      rcases ih (inScopeNames := collectStmtNames (.return value) ++ inScopeNames) with
        ⟨tailIR, htailIR⟩
      refine ⟨headIR ++ tailIR, ?_⟩
      rw [CompilationModel.compileStmtList, hheadIR]
      dsimp
      rw [htailIR]
      rfl
  case stop scope rest hrest ih =>
      rcases compileStmt_core_ok_any_scope (fields := fields) (inScopeNames := inScopeNames)
        (stmt := .stop) StmtCompileCore.stop with ⟨headIR, hheadIR⟩
      rcases ih (inScopeNames := collectStmtNames (.stop) ++ inScopeNames) with
        ⟨tailIR, htailIR⟩
      refine ⟨headIR ++ tailIR, ?_⟩
      rw [CompilationModel.compileStmtList, hheadIR]
      dsimp
      rw [htailIR]
      rfl

theorem compileStmtList_terminal_core_ok
    {fields : List Field}
    {scope inScopeNames : List String}
    {stmts : List Stmt}
    (hterminal : StmtListTerminalCore scope stmts) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames stmts = Except.ok bodyIR := by
  induction hterminal generalizing inScopeNames
  case letVar scope name value rest hvalue _ hrest ih =>
      rcases compileStmt_core_ok_any_scope (fields := fields) (inScopeNames := inScopeNames)
        (stmt := .letVar name value) (.letVar hvalue) with ⟨headIR, hheadIR⟩
      rcases ih (inScopeNames := collectStmtNames (.letVar name value) ++ inScopeNames) with
        ⟨tailIR, htailIR⟩
      refine ⟨headIR ++ tailIR, ?_⟩
      rw [CompilationModel.compileStmtList, hheadIR]
      dsimp
      rw [htailIR]
      rfl
  case assignVar scope name value rest hvalue _ hrest ih =>
      rcases compileStmt_core_ok_any_scope (fields := fields) (inScopeNames := inScopeNames)
        (stmt := .assignVar name value) (.assignVar hvalue) with ⟨headIR, hheadIR⟩
      rcases ih (inScopeNames := collectStmtNames (.assignVar name value) ++ inScopeNames) with
        ⟨tailIR, htailIR⟩
      refine ⟨headIR ++ tailIR, ?_⟩
      rw [CompilationModel.compileStmtList, hheadIR]
      dsimp
      rw [htailIR]
      rfl
  case require_ scope cond message rest hcond _ hrest ih =>
      rcases compileStmt_core_ok_any_scope (fields := fields) (inScopeNames := inScopeNames)
        (stmt := .require cond message) (.require_ hcond) with ⟨headIR, hheadIR⟩
      rcases ih (inScopeNames := collectStmtNames (.require cond message) ++ inScopeNames) with
        ⟨tailIR, htailIR⟩
      refine ⟨headIR ++ tailIR, ?_⟩
      rw [CompilationModel.compileStmtList, hheadIR]
      dsimp
      rw [htailIR]
      rfl
  case return_ scope value rest hvalue _ hrest =>
      rcases compileStmt_core_ok_any_scope (fields := fields) (inScopeNames := inScopeNames)
        (stmt := .return value) (.return_ hvalue) with ⟨headIR, hheadIR⟩
      rcases compileStmtList_core_ok (fields := fields)
          (scope := scope)
          (inScopeNames := collectStmtNames (.return value) ++ inScopeNames)
          (stmts := rest) hrest with
        ⟨tailIR, htailIR⟩
      refine ⟨headIR ++ tailIR, ?_⟩
      rw [CompilationModel.compileStmtList, hheadIR]
      dsimp
      rw [htailIR]
      rfl
  case stop scope rest hrest =>
      rcases compileStmt_core_ok_any_scope (fields := fields) (inScopeNames := inScopeNames)
        (stmt := .stop) StmtCompileCore.stop with ⟨headIR, hheadIR⟩
      rcases compileStmtList_core_ok (fields := fields)
          (scope := scope)
          (inScopeNames := collectStmtNames (.stop) ++ inScopeNames)
          (stmts := rest) hrest with
        ⟨tailIR, htailIR⟩
      refine ⟨headIR ++ tailIR, ?_⟩
      rw [CompilationModel.compileStmtList, hheadIR]
      dsimp
      rw [htailIR]
      rfl
  case ite scope cond thenBranch elseBranch rest hcond _ hthen helse hrest ihThen ihElse =>
      rcases compileExpr_core_ok (fields := fields) hcond with ⟨condIR, hcondIR⟩
      rcases ihThen (inScopeNames := inScopeNames) with ⟨thenIR, hthenIR⟩
      rcases ihElse (inScopeNames := inScopeNames) with ⟨elseIR, helseIR⟩
      rcases compileStmtList_core_ok (fields := fields)
          (scope := scope)
          (inScopeNames := collectStmtNames (.ite cond thenBranch elseBranch) ++ inScopeNames)
          (stmts := rest) hrest with
        ⟨tailIR, htailIR⟩
      have helseNonempty : elseBranch.isEmpty = false := by
        cases elseBranch with
        | nil =>
            exfalso
            exact stmtListTerminalCore_ne_nil helse rfl
        | cons =>
            simp
      refine
        ⟨[YulStmt.block [
            YulStmt.let_
              (CompilationModel.pickFreshName "__ite_cond"
                (inScopeNames ++ collectExprNames cond ++
                  collectStmtListNames thenBranch ++ collectStmtListNames elseBranch))
              condIR,
            YulStmt.if_
              (YulExpr.ident
                (CompilationModel.pickFreshName "__ite_cond"
                  (inScopeNames ++ collectExprNames cond ++
                    collectStmtListNames thenBranch ++ collectStmtListNames elseBranch)))
              thenIR,
            YulStmt.if_
              (YulExpr.call "iszero"
                [YulExpr.ident
                  (CompilationModel.pickFreshName "__ite_cond"
                    (inScopeNames ++ collectExprNames cond ++
                      collectStmtListNames thenBranch ++ collectStmtListNames elseBranch))])
              elseIR
          ]] ++ tailIR, ?_⟩
      rw [CompilationModel.compileStmtList]
      unfold CompilationModel.compileStmt
      rw [hcondIR, hthenIR, helseIR]
      dsimp
      rw [htailIR]
      simp [helseNonempty]
      rfl

theorem compileStmtList_terminal_core_ok_nonempty
    {fields : List Field}
    {scope inScopeNames : List String}
    {stmts : List Stmt}
    {bodyIR : List YulStmt}
    (hterminal : StmtListTerminalCore scope stmts)
    (hcompile :
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames stmts = Except.ok bodyIR) :
    bodyIR ≠ [] := by
  induction hterminal generalizing inScopeNames bodyIR with
  | letVar hvalue hinScope hrest ih =>
      rename_i scope name value rest
      rcases compileExpr_core_ok (fields := fields) hvalue with ⟨valueIR, hvalueIR⟩
      rcases compileStmtList_cons_ok_inv (fields := fields) (inScopeNames := inScopeNames)
          (stmt := .letVar name value) (rest := rest) hcompile with
        ⟨headIR, tailIR, hhead, _, hbody⟩
      rw [CompilationModel.compileStmt, hvalueIR] at hhead
      injection hhead with hheadEq
      subst hheadEq
      simp [hbody]
  | assignVar hvalue hinScope hrest ih =>
      rename_i scope name value rest
      rcases compileExpr_core_ok (fields := fields) hvalue with ⟨valueIR, hvalueIR⟩
      rcases compileStmtList_cons_ok_inv (fields := fields) (inScopeNames := inScopeNames)
          (stmt := .assignVar name value) (rest := rest) hcompile with
        ⟨headIR, tailIR, hhead, _, hbody⟩
      rw [CompilationModel.compileStmt, hvalueIR] at hhead
      injection hhead with hheadEq
      subst hheadEq
      simp [hbody]
  | require_ hcond hinScope hrest ih =>
      rename_i scope cond message rest
      rcases compileRequireFailCond_core_ok (fields := fields) hcond with ⟨failCond, hfailCond⟩
      rcases compileStmtList_cons_ok_inv (fields := fields) (inScopeNames := inScopeNames)
          (stmt := .require cond message) (rest := rest) hcompile with
        ⟨headIR, tailIR, hhead, _, hbody⟩
      rw [CompilationModel.compileStmt, hfailCond] at hhead
      injection hhead with hheadEq
      subst hheadEq
      simp [hbody]
  | return_ hvalue hinScope hrest =>
      rename_i scope value rest
      rcases compileExpr_core_ok (fields := fields) hvalue with ⟨valueIR, hvalueIR⟩
      rcases compileStmtList_cons_ok_inv (fields := fields) (inScopeNames := inScopeNames)
          (stmt := .return value) (rest := rest) hcompile with
        ⟨headIR, tailIR, hhead, _, hbody⟩
      rw [CompilationModel.compileStmt, hvalueIR] at hhead
      injection hhead with hheadEq
      subst hheadEq
      simp [hbody]
  | stop hrest =>
      rename_i scope rest
      rcases compileStmtList_cons_ok_inv (fields := fields) (inScopeNames := inScopeNames)
          (stmt := .stop) (rest := rest) hcompile with
        ⟨headIR, tailIR, hhead, _, hbody⟩
      rw [CompilationModel.compileStmt] at hhead
      injection hhead with hheadEq
      subst hheadEq
      simp [hbody]
  | ite hcond hinScope hthen helse hrest ihThen ihElse =>
      rename_i scope cond thenBranch elseBranch rest
      rcases compileStmtList_cons_ok_inv (fields := fields) (inScopeNames := inScopeNames)
          (stmt := .ite cond thenBranch elseBranch) (rest := rest) hcompile with
        ⟨headIR, tailIR, hhead, _, hbody⟩
      have helseNonempty : elseBranch.isEmpty = false := by
        cases elseBranch with
        | nil =>
            exfalso
            exact stmtListTerminalCore_ne_nil helse rfl
        | cons =>
            simp
      rcases compileExpr_core_ok (fields := fields) hcond with ⟨condIR', hcondOk⟩
      rcases compileStmtList_terminal_core_ok (fields := fields)
          (scope := scope) (inScopeNames := inScopeNames) (stmts := thenBranch) hthen with
        ⟨thenIR', hthenOk⟩
      rcases compileStmtList_terminal_core_ok (fields := fields)
          (scope := scope) (inScopeNames := inScopeNames) (stmts := elseBranch) helse with
        ⟨elseIR', helseOk⟩
      cases hcondIR : CompilationModel.compileExpr fields .calldata cond with
      | error err =>
          rw [hcondOk] at hcondIR
          cases hcondIR
      | ok condIR =>
          cases hthenIR :
              CompilationModel.compileStmtList
                fields [] [] .calldata [] false inScopeNames thenBranch with
          | error err =>
              rw [hthenOk] at hthenIR
              cases hthenIR
          | ok thenIR =>
              cases helseIR :
                  CompilationModel.compileStmtList
                    fields [] [] .calldata [] false inScopeNames elseBranch with
              | error err =>
                  rw [helseOk] at helseIR
                  cases helseIR
              | ok elseIR =>
                  simp [CompilationModel.compileStmt, helseNonempty, hcondIR, hthenIR, helseIR] at hhead
                  injection hhead with hheadEq
                  subst hheadEq
                  simp [hbody]

private theorem yulStmtList_length_le_sizeOf : (stmts : List YulStmt) → stmts.length ≤ sizeOf stmts
  | [] => by simp
  | _ :: rest => by
      have hrest := yulStmtList_length_le_sizeOf rest
      simp
      omega

private theorem compiledIteBlockSize_ge_thenBranchLength
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR : List YulStmt) :
    thenIR.length + 4 ≤
      sizeOf
        [ YulStmt.let_ tempName condIR
        , YulStmt.if_ (YulExpr.ident tempName) thenIR
        , YulStmt.if_
            (YulExpr.call "iszero" [YulExpr.ident tempName])
            elseIR ] := by
  have hthenLen : thenIR.length ≤ sizeOf thenIR :=
    yulStmtList_length_le_sizeOf thenIR
  simp
  omega

private theorem compiledIteBlockSize_ge_thenBranchSizeOf
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR : List YulStmt) :
    sizeOf thenIR + 4 ≤
      sizeOf
        [ YulStmt.let_ tempName condIR
        , YulStmt.if_ (YulExpr.ident tempName) thenIR
        , YulStmt.if_
            (YulExpr.call "iszero" [YulExpr.ident tempName])
            elseIR ] := by
  simp
  omega

private theorem compiledIteBlockSize_ge_thenBranchExecFuel
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR : List YulStmt) :
    sizeOf thenIR + 5 ≤
      sizeOf
        [ YulStmt.let_ tempName condIR
        , YulStmt.if_ (YulExpr.ident tempName) thenIR
        , YulStmt.if_
            (YulExpr.call "iszero" [YulExpr.ident tempName])
            elseIR ] := by
  simp
  omega

private theorem compiledIteBlockSize_ge_elseBranchLength
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR : List YulStmt) :
    elseIR.length + 4 ≤
      sizeOf
        [ YulStmt.let_ tempName condIR
        , YulStmt.if_ (YulExpr.ident tempName) thenIR
        , YulStmt.if_
            (YulExpr.call "iszero" [YulExpr.ident tempName])
            elseIR ] := by
  have helseLen : elseIR.length ≤ sizeOf elseIR :=
    yulStmtList_length_le_sizeOf elseIR
  simp
  omega

private theorem compiledIteBlockSize_ge_elseBranchSizeOf
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR : List YulStmt) :
    sizeOf elseIR + 4 ≤
      sizeOf
        [ YulStmt.let_ tempName condIR
        , YulStmt.if_ (YulExpr.ident tempName) thenIR
        , YulStmt.if_
            (YulExpr.call "iszero" [YulExpr.ident tempName])
            elseIR ] := by
  simp
  omega

private theorem compiledIteBlockSize_ge_elseBranchExecFuel
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR : List YulStmt) :
    sizeOf elseIR + 5 ≤
      sizeOf
        [ YulStmt.let_ tempName condIR
        , YulStmt.if_ (YulExpr.ident tempName) thenIR
        , YulStmt.if_
            (YulExpr.call "iszero" [YulExpr.ident tempName])
            elseIR ] := by
  simp
  omega

theorem compiled_terminal_ite_body_size_ge_branchFuel
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt) :
    thenIR.length + 4 ≤
      sizeOf
        ([YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_
                (YulExpr.call "iszero" [YulExpr.ident tempName])
                elseIR
            ]] ++ tailIR) ∧
    elseIR.length + 4 ≤
      sizeOf
        ([YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_
                (YulExpr.call "iszero" [YulExpr.ident tempName])
                elseIR
            ]] ++ tailIR) := by
  have hthen :
      thenIR.length + 4 ≤
        sizeOf
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_
              (YulExpr.call "iszero" [YulExpr.ident tempName])
              elseIR ] :=
    compiledIteBlockSize_ge_thenBranchLength tempName condIR thenIR elseIR
  have helse :
      elseIR.length + 4 ≤
        sizeOf
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_
              (YulExpr.call "iszero" [YulExpr.ident tempName])
              elseIR ] :=
    compiledIteBlockSize_ge_elseBranchLength tempName condIR thenIR elseIR
  constructor
  · simp at *
    omega
  · simp at *
    omega

theorem compiled_terminal_ite_body_size_ge_branchSizeOf
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt) :
    sizeOf thenIR + 4 ≤
      sizeOf
        ([YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_
                (YulExpr.call "iszero" [YulExpr.ident tempName])
                elseIR
            ]] ++ tailIR) ∧
    sizeOf elseIR + 4 ≤
      sizeOf
        ([YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_
                (YulExpr.call "iszero" [YulExpr.ident tempName])
                elseIR
            ]] ++ tailIR) := by
  have hthen :
      sizeOf thenIR + 4 ≤
        sizeOf
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_
              (YulExpr.call "iszero" [YulExpr.ident tempName])
              elseIR ] :=
    compiledIteBlockSize_ge_thenBranchSizeOf tempName condIR thenIR elseIR
  have helse :
      sizeOf elseIR + 4 ≤
        sizeOf
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_
              (YulExpr.call "iszero" [YulExpr.ident tempName])
              elseIR ] :=
    compiledIteBlockSize_ge_elseBranchSizeOf tempName condIR thenIR elseIR
  constructor
  · simp at *
    omega
  · simp at *
    omega

theorem compiled_terminal_ite_body_size_ge_branchExecFuel
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt) :
    sizeOf thenIR + 5 ≤
      sizeOf
        ([YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_
                (YulExpr.call "iszero" [YulExpr.ident tempName])
                elseIR
            ]] ++ tailIR) ∧
    sizeOf elseIR + 5 ≤
      sizeOf
        ([YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_
                (YulExpr.call "iszero" [YulExpr.ident tempName])
                elseIR
            ]] ++ tailIR) := by
  have hthen :
      sizeOf thenIR + 5 ≤
        sizeOf
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_
              (YulExpr.call "iszero" [YulExpr.ident tempName])
              elseIR ] :=
    compiledIteBlockSize_ge_thenBranchExecFuel tempName condIR thenIR elseIR
  have helse :
      sizeOf elseIR + 5 ≤
        sizeOf
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_
              (YulExpr.call "iszero" [YulExpr.ident tempName])
              elseIR ] :=
    compiledIteBlockSize_ge_elseBranchExecFuel tempName condIR thenIR elseIR
  constructor
  · simp at *
    omega
  · simp at *
    omega

theorem yulStmtList_sizeOf_cons_ge_tailFuel
    (stmt : YulStmt)
    (rest : List YulStmt) :
    sizeOf rest + 1 ≤ sizeOf (stmt :: rest) := by
  simp
  omega

theorem yulStmtList_sizeOf_cons_extraFuel_eq
    (extraFuel : Nat)
    (stmt : YulStmt)
    (rest : List YulStmt) :
    sizeOf (stmt :: rest) + extraFuel =
      sizeOf rest +
        (sizeOf (stmt :: rest) - (sizeOf rest + 1) + extraFuel) + 1 := by
  have htail : sizeOf rest + 1 ≤ sizeOf (stmt :: rest) :=
    yulStmtList_sizeOf_cons_ge_tailFuel stmt rest
  omega

theorem yulStmtList_sizeOf_cons_tailExecFuel_eq
    (extraFuel : Nat)
    (stmt : YulStmt)
    (rest : List YulStmt) :
    sizeOf rest +
        (sizeOf (stmt :: rest) - (sizeOf rest + 1) + extraFuel) =
      sizeOf (stmt :: rest) + extraFuel - 1 := by
  have htail : sizeOf rest + 1 ≤ sizeOf (stmt :: rest) :=
    yulStmtList_sizeOf_cons_ge_tailFuel stmt rest
  omega

theorem yulStmtList_sizeOf_two_cons_extraFuel_eq
    (extraFuel : Nat)
    (stmt1 stmt2 : YulStmt)
    (rest : List YulStmt) :
    sizeOf (stmt1 :: stmt2 :: rest) + extraFuel =
      sizeOf (stmt2 :: rest) +
        (sizeOf (stmt1 :: stmt2 :: rest) - (sizeOf (stmt2 :: rest) + 1) + extraFuel) + 1 := by
  have htail : sizeOf (stmt2 :: rest) + 1 ≤ sizeOf (stmt1 :: stmt2 :: rest) :=
    yulStmtList_sizeOf_cons_ge_tailFuel stmt1 (stmt2 :: rest)
  omega

theorem yulStmtList_sizeOf_two_cons_secondExecFuel_eq
    (extraFuel : Nat)
    (stmt1 stmt2 : YulStmt)
    (rest : List YulStmt) :
    sizeOf (stmt2 :: rest) +
        (sizeOf (stmt1 :: stmt2 :: rest) - (sizeOf (stmt2 :: rest) + 1) + extraFuel) =
      sizeOf (stmt1 :: stmt2 :: rest) + extraFuel - 1 := by
  have htail : sizeOf (stmt2 :: rest) + 1 ≤ sizeOf (stmt1 :: stmt2 :: rest) :=
    yulStmtList_sizeOf_cons_ge_tailFuel stmt1 (stmt2 :: rest)
  omega

theorem yulStmtList_sizeOf_two_cons_tail_extraFuel_eq
    (extraFuel : Nat)
    (stmt1 stmt2 : YulStmt)
    (rest : List YulStmt) :
    sizeOf (stmt2 :: rest) +
        (sizeOf (stmt1 :: stmt2 :: rest) - (sizeOf (stmt2 :: rest) + 1) + extraFuel) =
      sizeOf rest +
        (sizeOf (stmt2 :: rest) - (sizeOf rest + 1) +
          (sizeOf (stmt1 :: stmt2 :: rest) - (sizeOf (stmt2 :: rest) + 1) + extraFuel)) + 1 := by
  have htail : sizeOf rest + 1 ≤ sizeOf (stmt2 :: rest) :=
    yulStmtList_sizeOf_cons_ge_tailFuel stmt2 rest
  omega

theorem yulStmtList_sizeOf_two_cons_tailExecFuel_eq
    (extraFuel : Nat)
    (stmt1 stmt2 : YulStmt)
    (rest : List YulStmt) :
    sizeOf rest +
        (sizeOf (stmt2 :: rest) - (sizeOf rest + 1) +
          (sizeOf (stmt1 :: stmt2 :: rest) - (sizeOf (stmt2 :: rest) + 1) + extraFuel)) =
      sizeOf (stmt1 :: stmt2 :: rest) + extraFuel - 2 := by
  have htail₁ : sizeOf (stmt2 :: rest) + 1 ≤ sizeOf (stmt1 :: stmt2 :: rest) :=
    yulStmtList_sizeOf_cons_ge_tailFuel stmt1 (stmt2 :: rest)
  have htail₂ : sizeOf rest + 1 ≤ sizeOf (stmt2 :: rest) :=
    yulStmtList_sizeOf_cons_ge_tailFuel stmt2 rest
  omega

theorem yulStmtList_sizeOf_two_cons_wholeExecFuel_eq
    (extraFuel : Nat)
    (stmt1 stmt2 : YulStmt)
    (rest : List YulStmt) :
    sizeOf (stmt1 :: stmt2 :: rest) + extraFuel =
      sizeOf rest +
        (sizeOf (stmt2 :: rest) - (sizeOf rest + 1) +
          (sizeOf (stmt1 :: stmt2 :: rest) - (sizeOf (stmt2 :: rest) + 1) + extraFuel)) + 2 := by
  have htail₁ : sizeOf (stmt2 :: rest) + 1 ≤ sizeOf (stmt1 :: stmt2 :: rest) :=
    yulStmtList_sizeOf_cons_ge_tailFuel stmt1 (stmt2 :: rest)
  have htail₂ : sizeOf rest + 1 ≤ sizeOf (stmt2 :: rest) :=
    yulStmtList_sizeOf_cons_ge_tailFuel stmt2 rest
  omega

theorem compiled_terminal_ite_body_size_ge_blockFuel
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt) :
    sizeOf
        [ YulStmt.let_ tempName condIR
        , YulStmt.if_ (YulExpr.ident tempName) thenIR
        , YulStmt.if_
            (YulExpr.call "iszero" [YulExpr.ident tempName])
            elseIR ] + 2 ≤
      sizeOf
        ([YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_
                (YulExpr.call "iszero" [YulExpr.ident tempName])
                elseIR
            ]] ++ tailIR) := by
  simp
  omega

private theorem execIRStmts_cons_of_execIRStmt_continue
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt (rest.length + 1) state stmt = .continue next) :
    execIRStmts (rest.length + 2) state (stmt :: rest) =
      execIRStmts (rest.length + 1) next rest := by
  simp [execIRStmts, hstmt]

private theorem execIRStmts_cons_of_execIRStmt_continue_extraFuel
    (extraFuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt (rest.length + extraFuel + 1) state stmt = .continue next) :
    execIRStmts (rest.length + extraFuel + 2) state (stmt :: rest) =
      execIRStmts (rest.length + extraFuel + 1) next rest := by
  simp [execIRStmts, hstmt]

private theorem execIRStmts_cons_of_execIRStmt_continue_anyFuel
    (fuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt fuel state stmt = .continue next) :
    execIRStmts (fuel + 1) state (stmt :: rest) =
      execIRStmts fuel next rest := by
  cases fuel with
  | zero =>
      cases stmt with
      | funcDef name params rets body =>
          have hnext : next = state := by
            simpa [execIRStmt] using hstmt.symm
          subst hnext
          rfl
      | _ =>
          simp [execIRStmt] at hstmt
  | succ fuel =>
      simp [execIRStmts, hstmt]

private theorem execIRStmts_cons_of_execIRStmt_continue_stepFuel
    (fuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt (fuel + 1) state stmt = .continue next) :
    execIRStmts (fuel + 2) state (stmt :: rest) =
      execIRStmts (fuel + 1) next rest := by
  simpa [Nat.add_assoc] using
    (execIRStmts_cons_of_execIRStmt_continue_anyFuel
      (fuel := fuel + 1)
      (state := state)
      (next := next)
      (stmt := stmt)
      (rest := rest)
      hstmt)

private theorem execIRStmts_cons_of_execIRStmt_continue_wholeFuel
    (extraFuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt (sizeOf (stmt :: rest) + extraFuel) state stmt = .continue next) :
    execIRStmts (sizeOf (stmt :: rest) + extraFuel + 1) state (stmt :: rest) =
      execIRStmts (sizeOf (stmt :: rest) + extraFuel) next rest := by
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (execIRStmts_cons_of_execIRStmt_continue_anyFuel
      (fuel := sizeOf (stmt :: rest) + extraFuel)
      (state := state)
      (next := next)
      (stmt := stmt)
      (rest := rest)
      hstmt)

private theorem execIRStmts_singleton_append_of_execIRStmt_continue_wholeFuel
    (extraFuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt (sizeOf ([stmt] ++ rest) + extraFuel) state stmt = .continue next) :
    execIRStmts (sizeOf ([stmt] ++ rest) + extraFuel + 1) state ([stmt] ++ rest) =
      execIRStmts (sizeOf ([stmt] ++ rest) + extraFuel) next rest := by
  simpa using
    (execIRStmts_cons_of_execIRStmt_continue_wholeFuel
      (extraFuel := extraFuel)
      (state := state)
      (next := next)
      (stmt := stmt)
      (rest := rest)
      hstmt)

private theorem execIRStmts_singleton_append_of_execIRStmt_continue_tailExtraFuel
    (extraFuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (irExec : IRExecResult)
    (hstmt : execIRStmt (sizeOf ([stmt] ++ rest) + extraFuel) state stmt = .continue next)
    (htail :
      execIRStmts
        (sizeOf rest +
          (sizeOf ([stmt] ++ rest) - (sizeOf rest + 1) + extraFuel) + 1)
        next rest = irExec) :
    execIRStmts (sizeOf ([stmt] ++ rest) + extraFuel + 1) state ([stmt] ++ rest) = irExec := by
  rw [execIRStmts_singleton_append_of_execIRStmt_continue_wholeFuel
      (extraFuel := extraFuel)
      (state := state)
      (next := next)
      (stmt := stmt)
      (rest := rest)
      hstmt]
  have hfuelEq :
      sizeOf rest +
          (sizeOf ([stmt] ++ rest) - (sizeOf rest + 1) + extraFuel) + 1 =
        sizeOf ([stmt] ++ rest) + extraFuel := by
    simpa using (yulStmtList_sizeOf_cons_extraFuel_eq extraFuel stmt rest).symm
  rw [hfuelEq] at htail
  exact htail

private theorem execIRStmts_cons_of_execIRStmt_return
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt) (value : Nat)
    (hstmt : execIRStmt (rest.length + 1) state stmt = .return value next) :
    execIRStmts (rest.length + 2) state (stmt :: rest) =
      .return value next := by
  simp [execIRStmts, hstmt]

private theorem execIRStmts_cons_of_execIRStmt_return_extraFuel
    (extraFuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt) (value : Nat)
    (hstmt : execIRStmt (rest.length + extraFuel + 1) state stmt = .return value next) :
    execIRStmts (rest.length + extraFuel + 2) state (stmt :: rest) =
      .return value next := by
  simp [execIRStmts, hstmt]

private theorem execIRStmts_cons_of_execIRStmt_return_anyFuel
    (fuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt) (value : Nat)
    (hstmt : execIRStmt fuel state stmt = .return value next) :
    execIRStmts (fuel + 1) state (stmt :: rest) =
      .return value next := by
  cases fuel with
  | zero =>
      cases stmt <;> simp [execIRStmt, execIRStmts] at hstmt ⊢ <;> simpa using hstmt
  | succ fuel =>
      simp [execIRStmts, hstmt]

private theorem execIRStmts_cons_of_execIRStmt_return_stepFuel
    (fuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt) (value : Nat)
    (hstmt : execIRStmt (fuel + 1) state stmt = .return value next) :
    execIRStmts (fuel + 2) state (stmt :: rest) =
      .return value next := by
  simpa [Nat.add_assoc] using
    (execIRStmts_cons_of_execIRStmt_return_anyFuel
      (fuel := fuel + 1)
      (state := state)
      (next := next)
      (stmt := stmt)
      (rest := rest)
      (value := value)
      hstmt)

private theorem execIRStmts_cons_of_execIRStmt_return_wholeFuel
    (extraFuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt) (value : Nat)
    (hstmt : execIRStmt (sizeOf (stmt :: rest) + extraFuel) state stmt = .return value next) :
    execIRStmts (sizeOf (stmt :: rest) + extraFuel + 1) state (stmt :: rest) =
      .return value next := by
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (execIRStmts_cons_of_execIRStmt_return_anyFuel
      (fuel := sizeOf (stmt :: rest) + extraFuel)
      (state := state)
      (next := next)
      (stmt := stmt)
      (rest := rest)
      (value := value)
      hstmt)

private theorem execIRStmts_singleton_append_of_execIRStmt_return_wholeFuel
    (extraFuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt) (value : Nat)
    (hstmt : execIRStmt (sizeOf ([stmt] ++ rest) + extraFuel) state stmt = .return value next) :
    execIRStmts (sizeOf ([stmt] ++ rest) + extraFuel + 1) state ([stmt] ++ rest) =
      .return value next := by
  simpa using
    (execIRStmts_cons_of_execIRStmt_return_wholeFuel
      (extraFuel := extraFuel)
      (state := state)
      (next := next)
      (stmt := stmt)
      (rest := rest)
      (value := value)
      hstmt)

private theorem execIRStmts_cons_of_execIRStmt_stop
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt (rest.length + 1) state stmt = .stop next) :
    execIRStmts (rest.length + 2) state (stmt :: rest) =
      .stop next := by
  simp [execIRStmts, hstmt]

private theorem execIRStmts_cons_of_execIRStmt_stop_extraFuel
    (extraFuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt (rest.length + extraFuel + 1) state stmt = .stop next) :
    execIRStmts (rest.length + extraFuel + 2) state (stmt :: rest) =
      .stop next := by
  simp [execIRStmts, hstmt]

private theorem execIRStmts_cons_of_execIRStmt_stop_anyFuel
    (fuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt fuel state stmt = .stop next) :
    execIRStmts (fuel + 1) state (stmt :: rest) =
      .stop next := by
  cases fuel with
  | zero =>
      cases stmt <;> simp [execIRStmt, execIRStmts] at hstmt ⊢ <;> simpa using hstmt
  | succ fuel =>
      simp [execIRStmts, hstmt]

private theorem execIRStmts_cons_of_execIRStmt_stop_stepFuel
    (fuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt (fuel + 1) state stmt = .stop next) :
    execIRStmts (fuel + 2) state (stmt :: rest) =
      .stop next := by
  simpa [Nat.add_assoc] using
    (execIRStmts_cons_of_execIRStmt_stop_anyFuel
      (fuel := fuel + 1)
      (state := state)
      (next := next)
      (stmt := stmt)
      (rest := rest)
      hstmt)

private theorem execIRStmts_cons_of_execIRStmt_stop_wholeFuel
    (extraFuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt (sizeOf (stmt :: rest) + extraFuel) state stmt = .stop next) :
    execIRStmts (sizeOf (stmt :: rest) + extraFuel + 1) state (stmt :: rest) =
      .stop next := by
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (execIRStmts_cons_of_execIRStmt_stop_anyFuel
      (fuel := sizeOf (stmt :: rest) + extraFuel)
      (state := state)
      (next := next)
      (stmt := stmt)
      (rest := rest)
      hstmt)

private theorem execIRStmts_singleton_append_of_execIRStmt_stop_wholeFuel
    (extraFuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt (sizeOf ([stmt] ++ rest) + extraFuel) state stmt = .stop next) :
    execIRStmts (sizeOf ([stmt] ++ rest) + extraFuel + 1) state ([stmt] ++ rest) =
      .stop next := by
  simpa using
    (execIRStmts_cons_of_execIRStmt_stop_wholeFuel
      (extraFuel := extraFuel)
      (state := state)
      (next := next)
      (stmt := stmt)
      (rest := rest)
      hstmt)

private theorem execIRStmts_cons_of_execIRStmt_revert
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt (rest.length + 1) state stmt = .revert next) :
    execIRStmts (rest.length + 2) state (stmt :: rest) =
      .revert next := by
  simp [execIRStmts, hstmt]

private theorem execIRStmts_cons_of_execIRStmt_revert_extraFuel
    (extraFuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt (rest.length + extraFuel + 1) state stmt = .revert next) :
    execIRStmts (rest.length + extraFuel + 2) state (stmt :: rest) =
      .revert next := by
  simp [execIRStmts, hstmt]

private theorem execIRStmts_cons_of_execIRStmt_revert_anyFuel
    (fuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt fuel state stmt = .revert next) :
    execIRStmts (fuel + 1) state (stmt :: rest) =
      .revert next := by
  cases fuel with
  | zero =>
      cases stmt <;> simp [execIRStmt, execIRStmts] at hstmt ⊢ <;> simpa using hstmt
  | succ fuel =>
      simp [execIRStmts, hstmt]

private theorem execIRStmts_cons_of_execIRStmt_revert_stepFuel
    (fuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt (fuel + 1) state stmt = .revert next) :
    execIRStmts (fuel + 2) state (stmt :: rest) =
      .revert next := by
  simpa [Nat.add_assoc] using
    (execIRStmts_cons_of_execIRStmt_revert_anyFuel
      (fuel := fuel + 1)
      (state := state)
      (next := next)
      (stmt := stmt)
      (rest := rest)
      hstmt)

private theorem execIRStmts_cons_of_execIRStmt_revert_wholeFuel
    (extraFuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt (sizeOf (stmt :: rest) + extraFuel) state stmt = .revert next) :
    execIRStmts (sizeOf (stmt :: rest) + extraFuel + 1) state (stmt :: rest) =
      .revert next := by
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (execIRStmts_cons_of_execIRStmt_revert_anyFuel
      (fuel := sizeOf (stmt :: rest) + extraFuel)
      (state := state)
      (next := next)
      (stmt := stmt)
      (rest := rest)
      hstmt)

private theorem execIRStmts_singleton_append_of_execIRStmt_revert_wholeFuel
    (extraFuel : Nat)
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt (sizeOf ([stmt] ++ rest) + extraFuel) state stmt = .revert next) :
    execIRStmts (sizeOf ([stmt] ++ rest) + extraFuel + 1) state ([stmt] ++ rest) =
      .revert next := by
  simpa using
    (execIRStmts_cons_of_execIRStmt_revert_wholeFuel
      (extraFuel := extraFuel)
      (state := state)
      (next := next)
      (stmt := stmt)
      (rest := rest)
      hstmt)

private theorem execIRStmts_two_of_execIRStmt_continue
    (state mid : IRState) (stmt1 stmt2 : YulStmt) (rest : List YulStmt)
    (hstmt1 : execIRStmt (rest.length + 2) state stmt1 = .continue mid) :
    execIRStmts (rest.length + 3) state (stmt1 :: stmt2 :: rest) =
      execIRStmts (rest.length + 2) mid (stmt2 :: rest) := by
  simp [execIRStmts, hstmt1]

private theorem execIRStmts_two_of_execIRStmt_continue_extraFuel
    (extraFuel : Nat)
    (state mid : IRState) (stmt1 stmt2 : YulStmt) (rest : List YulStmt)
    (hstmt1 : execIRStmt (rest.length + extraFuel + 2) state stmt1 = .continue mid) :
    execIRStmts (rest.length + extraFuel + 3) state (stmt1 :: stmt2 :: rest) =
      execIRStmts (rest.length + extraFuel + 2) mid (stmt2 :: rest) := by
  simp [execIRStmts, hstmt1]

private theorem execIRStmts_two_of_continue_then_return
    (state mid next : IRState) (stmt1 stmt2 : YulStmt) (rest : List YulStmt) (value : Nat)
    (hstmt1 : execIRStmt (rest.length + 2) state stmt1 = .continue mid)
    (hstmt2 : execIRStmt (rest.length + 1) mid stmt2 = .return value next) :
    execIRStmts (rest.length + 3) state (stmt1 :: stmt2 :: rest) =
      .return value next := by
  rw [execIRStmts_two_of_execIRStmt_continue state mid stmt1 stmt2 rest hstmt1]
  exact execIRStmts_cons_of_execIRStmt_return mid next stmt2 rest value hstmt2

private theorem execIRStmts_two_of_continue_then_return_extraFuel
    (extraFuel : Nat)
    (state mid next : IRState) (stmt1 stmt2 : YulStmt) (rest : List YulStmt) (value : Nat)
    (hstmt1 : execIRStmt (rest.length + extraFuel + 2) state stmt1 = .continue mid)
    (hstmt2 : execIRStmt (rest.length + extraFuel + 1) mid stmt2 = .return value next) :
    execIRStmts (rest.length + extraFuel + 3) state (stmt1 :: stmt2 :: rest) =
      .return value next := by
  rw [execIRStmts_two_of_execIRStmt_continue_extraFuel extraFuel state mid stmt1 stmt2 rest hstmt1]
  exact execIRStmts_cons_of_execIRStmt_return_extraFuel extraFuel mid next stmt2 rest value hstmt2

private theorem execIRStmts_two_of_continue_then_return_anyFuel
    (fuel : Nat)
    (state mid next : IRState) (stmt1 stmt2 : YulStmt) (rest : List YulStmt) (value : Nat)
    (hstmt1 : execIRStmt fuel state stmt1 = .continue mid)
    (hstmt2 : execIRStmt (fuel - 1) mid stmt2 = .return value next) :
    execIRStmts (fuel + 1) state (stmt1 :: stmt2 :: rest) =
      .return value next := by
  rw [execIRStmts_cons_of_execIRStmt_continue_anyFuel fuel state mid stmt1 (stmt2 :: rest) hstmt1]
  cases fuel with
  | zero =>
      cases stmt2 <;> simp [execIRStmt] at hstmt2
  | succ fuel =>
      simpa using
        (execIRStmts_cons_of_execIRStmt_return_anyFuel fuel mid next stmt2 rest value hstmt2)

private theorem execIRStmts_two_of_continue_then_return_stepFuel
    (fuel : Nat)
    (state mid next : IRState) (stmt1 stmt2 : YulStmt) (rest : List YulStmt) (value : Nat)
    (hstmt1 : execIRStmt (fuel + 2) state stmt1 = .continue mid)
    (hstmt2 : execIRStmt (fuel + 1) mid stmt2 = .return value next) :
    execIRStmts (fuel + 3) state (stmt1 :: stmt2 :: rest) =
      .return value next := by
  simpa [Nat.add_assoc] using
    (execIRStmts_two_of_continue_then_return_anyFuel
      (fuel := fuel + 2)
      (state := state)
      (mid := mid)
      (next := next)
      (stmt1 := stmt1)
      (stmt2 := stmt2)
      (rest := rest)
      (value := value)
      hstmt1
      (by simpa [Nat.add_assoc] using hstmt2))

private theorem execIRStmts_two_of_continue_then_return_wholeFuel
    (extraFuel : Nat)
    (state mid next : IRState) (stmt1 stmt2 : YulStmt) (rest : List YulStmt) (value : Nat)
    (hstmt1 :
      execIRStmt (sizeOf (stmt1 :: stmt2 :: rest) + extraFuel) state stmt1 = .continue mid)
    (hstmt2 :
      execIRStmt (sizeOf (stmt1 :: stmt2 :: rest) + extraFuel - 1) mid stmt2 =
        .return value next) :
    execIRStmts (sizeOf (stmt1 :: stmt2 :: rest) + extraFuel + 1) state (stmt1 :: stmt2 :: rest) =
      .return value next := by
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (execIRStmts_two_of_continue_then_return_anyFuel
      (fuel := sizeOf (stmt1 :: stmt2 :: rest) + extraFuel)
      (state := state)
      (mid := mid)
      (next := next)
      (stmt1 := stmt1)
      (stmt2 := stmt2)
      (rest := rest)
      (value := value)
      hstmt1
      hstmt2)

private theorem execIRStmts_two_append_of_continue_then_return_wholeFuel
    (extraFuel : Nat)
    (state mid next : IRState) (stmt1 stmt2 : YulStmt) (rest : List YulStmt) (value : Nat)
    (hstmt1 :
      execIRStmt (sizeOf ([stmt1, stmt2] ++ rest) + extraFuel) state stmt1 = .continue mid)
    (hstmt2 :
      execIRStmt (sizeOf ([stmt1, stmt2] ++ rest) + extraFuel - 1) mid stmt2 =
        .return value next) :
    execIRStmts (sizeOf ([stmt1, stmt2] ++ rest) + extraFuel + 1) state ([stmt1, stmt2] ++ rest) =
      .return value next := by
  simpa using
    (execIRStmts_two_of_continue_then_return_wholeFuel
      (extraFuel := extraFuel)
      (state := state)
      (mid := mid)
      (next := next)
      (stmt1 := stmt1)
      (stmt2 := stmt2)
      (rest := rest)
      (value := value)
      hstmt1
      hstmt2)

private theorem execIRStmt_block_of_execIRStmts_continue
    (fuel : Nat) (state next : IRState) (body : List YulStmt)
    (hbody : execIRStmts fuel state body = .continue next) :
    execIRStmt (Nat.succ fuel) state (YulStmt.block body) = .continue next := by
  simpa [execIRStmt] using hbody

private theorem execIRStmt_block_of_execIRStmts_continue_nonzeroFuel
    (fuel : Nat) (state next : IRState) (body : List YulStmt)
    (hfuel : fuel ≠ 0)
    (hbody : execIRStmts (fuel - 1) state body = .continue next) :
    execIRStmt fuel state (YulStmt.block body) = .continue next := by
  cases fuel with
  | zero =>
      exact False.elim (hfuel rfl)
  | succ fuel =>
      simpa using execIRStmt_block_of_execIRStmts_continue fuel state next body hbody

private theorem execIRStmt_block_of_execIRStmts_return
    (fuel : Nat) (state next : IRState) (body : List YulStmt) (value : Nat)
    (hbody : execIRStmts fuel state body = .return value next) :
    execIRStmt (Nat.succ fuel) state (YulStmt.block body) = .return value next := by
  simpa [execIRStmt] using hbody

private theorem execIRStmt_block_of_execIRStmts_return_nonzeroFuel
    (fuel : Nat) (state next : IRState) (body : List YulStmt) (value : Nat)
    (hfuel : fuel ≠ 0)
    (hbody : execIRStmts (fuel - 1) state body = .return value next) :
    execIRStmt fuel state (YulStmt.block body) = .return value next := by
  cases fuel with
  | zero =>
      exact False.elim (hfuel rfl)
  | succ fuel =>
      simpa using execIRStmt_block_of_execIRStmts_return fuel state next body value hbody

private theorem execIRStmt_block_of_execIRStmts_stop
    (fuel : Nat) (state next : IRState) (body : List YulStmt)
    (hbody : execIRStmts fuel state body = .stop next) :
    execIRStmt (Nat.succ fuel) state (YulStmt.block body) = .stop next := by
  simpa [execIRStmt] using hbody

private theorem execIRStmt_block_of_execIRStmts_stop_nonzeroFuel
    (fuel : Nat) (state next : IRState) (body : List YulStmt)
    (hfuel : fuel ≠ 0)
    (hbody : execIRStmts (fuel - 1) state body = .stop next) :
    execIRStmt fuel state (YulStmt.block body) = .stop next := by
  cases fuel with
  | zero =>
      exact False.elim (hfuel rfl)
  | succ fuel =>
      simpa using execIRStmt_block_of_execIRStmts_stop fuel state next body hbody

private theorem execIRStmt_block_of_execIRStmts_revert
    (fuel : Nat) (state next : IRState) (body : List YulStmt)
    (hbody : execIRStmts fuel state body = .revert next) :
    execIRStmt (Nat.succ fuel) state (YulStmt.block body) = .revert next := by
  simpa [execIRStmt] using hbody

private theorem execIRStmt_block_of_execIRStmts_revert_nonzeroFuel
    (fuel : Nat) (state next : IRState) (body : List YulStmt)
    (hfuel : fuel ≠ 0)
    (hbody : execIRStmts (fuel - 1) state body = .revert next) :
    execIRStmt fuel state (YulStmt.block body) = .revert next := by
  cases fuel with
  | zero =>
      exact False.elim (hfuel rfl)
  | succ fuel =>
      simpa using execIRStmt_block_of_execIRStmts_revert fuel state next body hbody

private theorem execIRStmt_if_true_of_eval
    (fuel : Nat) (state : IRState) (cond : YulExpr) (body : List YulStmt) (value : Nat)
    (hcond : evalIRExpr state cond = some value)
    (hvalue : value ≠ 0) :
    execIRStmt (Nat.succ fuel) state (YulStmt.if_ cond body) = execIRStmts fuel state body := by
  simp [execIRStmt, hcond, hvalue]

private theorem execIRStmt_if_true_of_eval_nonzeroFuel
    (fuel : Nat) (state : IRState) (cond : YulExpr) (body : List YulStmt) (value : Nat)
    (hfuel : fuel ≠ 0)
    (hcond : evalIRExpr state cond = some value)
    (hvalue : value ≠ 0) :
    execIRStmt fuel state (YulStmt.if_ cond body) = execIRStmts (fuel - 1) state body := by
  cases fuel with
  | zero =>
      exact False.elim (hfuel rfl)
  | succ fuel =>
      simpa using execIRStmt_if_true_of_eval fuel state cond body value hcond hvalue

private theorem execIRStmt_if_false_of_eval
    (fuel : Nat) (state : IRState) (cond : YulExpr) (body : List YulStmt) (value : Nat)
    (hcond : evalIRExpr state cond = some value)
    (hvalue : value = 0) :
    execIRStmt (Nat.succ fuel) state (YulStmt.if_ cond body) = .continue state := by
  simp [execIRStmt, hcond, hvalue]

private theorem execIRStmt_if_false_of_eval_nonzeroFuel
    (fuel : Nat) (state : IRState) (cond : YulExpr) (body : List YulStmt) (value : Nat)
    (hfuel : fuel ≠ 0)
    (hcond : evalIRExpr state cond = some value)
    (hvalue : value = 0) :
    execIRStmt fuel state (YulStmt.if_ cond body) = .continue state := by
  cases fuel with
  | zero =>
      exact False.elim (hfuel rfl)
  | succ fuel =>
      simpa using execIRStmt_if_false_of_eval fuel state cond body value hcond hvalue

private theorem execIRStmt_let_of_eval_anyFuel
    (fuel : Nat)
    (state : IRState)
    (name : String)
    (valueExpr : YulExpr)
    (value : Nat)
    (heval : evalIRExpr state valueExpr = some value) :
    execIRStmt (Nat.succ fuel) state (YulStmt.let_ name valueExpr) =
      .continue (state.setVar name value) := by
  simp [execIRStmt, heval]

private theorem execIRStmt_let_of_eval_nonzeroFuel
    (fuel : Nat)
    (state : IRState)
    (name : String)
    (valueExpr : YulExpr)
    (value : Nat)
    (hfuel : fuel ≠ 0)
    (heval : evalIRExpr state valueExpr = some value) :
    execIRStmt fuel state (YulStmt.let_ name valueExpr) =
      .continue (state.setVar name value) := by
  cases fuel with
  | zero =>
      exact False.elim (hfuel rfl)
  | succ fuel =>
      simpa using execIRStmt_let_of_eval_anyFuel fuel state name valueExpr value heval

private theorem execIRStmt_assign_of_eval_anyFuel
    (fuel : Nat)
    (state : IRState)
    (name : String)
    (valueExpr : YulExpr)
    (value : Nat)
    (heval : evalIRExpr state valueExpr = some value) :
    execIRStmt (Nat.succ fuel) state (YulStmt.assign name valueExpr) =
      .continue (state.setVar name value) := by
  simp [execIRStmt, heval]

private theorem execIRStmt_assign_of_eval_nonzeroFuel
    (fuel : Nat)
    (state : IRState)
    (name : String)
    (valueExpr : YulExpr)
    (value : Nat)
    (hfuel : fuel ≠ 0)
    (heval : evalIRExpr state valueExpr = some value) :
    execIRStmt fuel state (YulStmt.assign name valueExpr) =
      .continue (state.setVar name value) := by
  cases fuel with
  | zero =>
      exact False.elim (hfuel rfl)
  | succ fuel =>
      simpa using execIRStmt_assign_of_eval_anyFuel fuel state name valueExpr value heval

private theorem execIRStmt_mstore_of_eval_anyFuel
    (fuel : Nat)
    (state : IRState)
    (offset : Nat)
    (valueExpr : YulExpr)
    (value : Nat)
    (heval : evalIRExpr state valueExpr = some value) :
    execIRStmt (Nat.succ fuel) state
      (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit offset, valueExpr])) =
      .continue { state with memory := fun o => if o = offset then value else state.memory o } := by
  simp [execIRStmt, evalIRExpr, heval]

private theorem execIRStmt_mstore_of_eval_nonzeroFuel
    (fuel : Nat)
    (state : IRState)
    (offset : Nat)
    (valueExpr : YulExpr)
    (value : Nat)
    (hfuel : fuel ≠ 0)
    (heval : evalIRExpr state valueExpr = some value) :
    execIRStmt fuel state
      (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit offset, valueExpr])) =
      .continue { state with memory := fun o => if o = offset then value else state.memory o } := by
  cases fuel with
  | zero =>
      exact False.elim (hfuel rfl)
  | succ fuel =>
      simpa using execIRStmt_mstore_of_eval_anyFuel fuel state offset valueExpr value heval

private theorem execIRStmt_return32_of_memory_anyFuel
    (fuel : Nat)
    (state : IRState)
    (offset : Nat) :
    execIRStmt (Nat.succ fuel) state
      (YulStmt.expr (YulExpr.call "return" [YulExpr.lit offset, YulExpr.lit 32])) =
      .return (state.memory offset) state := by
  simp [execIRStmt, evalIRExpr]

private theorem execIRStmt_return32_of_memory_nonzeroFuel
    (fuel : Nat)
    (state : IRState)
    (offset : Nat)
    (hfuel : fuel ≠ 0) :
    execIRStmt fuel state
      (YulStmt.expr (YulExpr.call "return" [YulExpr.lit offset, YulExpr.lit 32])) =
      .return (state.memory offset) state := by
  cases fuel with
  | zero =>
      exact False.elim (hfuel rfl)
  | succ fuel =>
      simpa using execIRStmt_return32_of_memory_anyFuel fuel state offset

private theorem execIRStmt_stop_nonzeroFuel
    (fuel : Nat)
    (state : IRState)
    (hfuel : fuel ≠ 0) :
    execIRStmt fuel state (YulStmt.expr (YulExpr.call "stop" [])) = .stop state := by
  cases fuel with
  | zero =>
      exact False.elim (hfuel rfl)
  | succ fuel =>
      simpa using execIRStmt_stop_succ fuel state

private theorem evalIRExpr_iszero_of_eval
    (state : IRState)
    (expr : YulExpr)
    (value : Nat)
    (heval : evalIRExpr state expr = some value)
    (hvalueLt : value < Compiler.Constants.evmModulus) :
    evalIRExpr state (YulExpr.call "iszero" [expr]) =
      some (if value = 0 then 1 else 0) := by
  simpa [boolWord_eq_if] using evalIRExpr_iszero_of_lt heval hvalueLt

private inductive RevertPrefixStmt : YulStmt → Prop where
  | mstore_lit {offset value : Nat} :
      RevertPrefixStmt (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit offset, YulExpr.lit value]))
  | mstore_hex {offset value : Nat} :
      RevertPrefixStmt (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit offset, YulExpr.hex value]))

private theorem execIRStmt_revertPrefix_continue
    (fuel : Nat) (state : IRState) {stmt : YulStmt}
    (hstmt : RevertPrefixStmt stmt) :
    ∃ next, execIRStmt (Nat.succ fuel) state stmt = .continue next := by
  cases hstmt with
  | mstore_lit =>
      rename_i offset value
      let next :=
        { state with
          memory := fun o => if o = offset then value else state.memory o }
      refine ⟨next, ?_⟩
      simp [execIRStmt, evalIRExpr, next]
  | mstore_hex =>
      rename_i offset value
      let next :=
        { state with
          memory := fun o => if o = offset then value else state.memory o }
      refine ⟨next, ?_⟩
      simp [execIRStmt, evalIRExpr, next]

private theorem execIRStmts_revertPrefix_then_revert
    (fuel : Nat) (state : IRState)
    (prefixStmts : List YulStmt)
    (offset size : Nat)
    (hprefix : ∀ stmt ∈ prefixStmts, RevertPrefixStmt stmt) :
    ∃ next,
      execIRStmts fuel state
        (prefixStmts ++ [YulStmt.expr (YulExpr.call "revert" [YulExpr.lit offset, YulExpr.lit size])]) =
          .revert next := by
  induction fuel generalizing state prefixStmts with
  | zero =>
      cases prefixStmts <;> refine ⟨state, ?_⟩ <;> simp [execIRStmts]
  | succ fuel ih =>
      cases prefixStmts with
      | nil =>
          refine ⟨state, ?_⟩
          cases fuel <;> simp [execIRStmts, execIRStmt]
      | cons stmt rest =>
          have hstmtPred : RevertPrefixStmt stmt := hprefix stmt (by simp)
          cases fuel with
          | zero =>
              cases hstmtPred <;> refine ⟨state, ?_⟩ <;> simp [execIRStmts, execIRStmt]
          | succ fuel =>
              rcases execIRStmt_revertPrefix_continue fuel state hstmtPred with ⟨mid, hstmt⟩
              have hrestPred : ∀ stmt' ∈ rest, RevertPrefixStmt stmt' := by
                intro stmt' hmem
                exact hprefix stmt' (by simp [hmem])
              rcases ih mid rest hrestPred with ⟨next, hrestExec⟩
              refine ⟨next, ?_⟩
              simp [execIRStmts, hstmt, hrestExec]

private theorem execIRStmts_revertWithMessage_revert
    (fuel : Nat) (state : IRState) (message : String) :
    ∃ next,
      execIRStmts fuel state (CompilationModel.revertWithMessage message) = .revert next := by
  let bytes := CompilationModel.bytesFromString message
  let len := bytes.length
  let paddedLen := ((len + 31) / 32) * 32
  let header := [
    YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.hex errorStringSelectorWord]),
    YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 4, YulExpr.lit 32]),
    YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 36, YulExpr.lit len])
  ]
  let dataStmts :=
    (CompilationModel.chunkBytes32 bytes).zipIdx.map fun (chunk, idx) =>
      let offset := 68 + idx * 32
      let word := CompilationModel.wordFromBytes chunk
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit offset, YulExpr.hex word])
  have hprefix : ∀ stmt ∈ header ++ dataStmts, RevertPrefixStmt stmt := by
    intro stmt hmem
    rcases List.mem_append.mp hmem with hhead | hdata
    · simp [header] at hhead
      rcases hhead with rfl | rfl | rfl
      · exact RevertPrefixStmt.mstore_hex
      · exact RevertPrefixStmt.mstore_lit
      · exact RevertPrefixStmt.mstore_lit
    · unfold dataStmts at hdata
      simp only [List.mem_map] at hdata
      rcases hdata with ⟨pair, _, rfl⟩
      exact RevertPrefixStmt.mstore_hex
  simpa [CompilationModel.revertWithMessage, bytes, len, paddedLen, header, dataStmts,
    List.append_assoc] using
    execIRStmts_revertPrefix_then_revert (fuel := fuel) (state := state)
      (prefixStmts := header ++ dataStmts) (offset := 0) (size := 68 + paddedLen) hprefix

theorem exec_compileStmtList_core
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope inScopeNames : List String}
    {stmts : List Stmt}
    (hcore : StmtListCompileCore scope stmts)
    (hscope : scopeNamesPresent scope runtime.bindings)
    (hexact : bindingsExactlyMatchIRVars runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames stmts = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmtList fields runtime stmts
      let irExec := execIRStmts (bodyIR.length + 1) state bodyIR
      stmtResultMatchesIRExec fields sourceResult irExec ∧
      stmtResultMatchesIRExecExact sourceResult irExec := by
   induction hcore generalizing runtime state inScopeNames with
   | nil =>
       refine ⟨[], rfl, ?_⟩
       constructor
       · simpa [SourceSemantics.execStmtList, execIRStmts, stmtResultMatchesIRExec] using hruntime
       · simpa [SourceSemantics.execStmtList, execIRStmts, stmtResultMatchesIRExecExact] using
           And.intro hexact hbounded
   | letVar hvalue hinScope hrest ih =>
       rename_i scope name value rest
       have hpresent : exprBoundNamesPresent value runtime.bindings :=
         exprBoundNamesPresent_of_scope hscope hinScope
       rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
       let valueNat := SourceSemantics.evalExpr fields runtime value
       let runtime' :=
         { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
       let state' := state.setVar name valueNat
       have heval := eval_compileExpr_core hvalue hexact hbounded hpresent hruntime
       rw [hvalueIR] at heval
       have heval' : evalIRExpr state valueIR = some valueNat := by
         simpa [valueNat] using heval
       have hvalueLt := evalExpr_lt_evmModulus_core hvalue hexact hbounded hpresent hruntime
       have hruntime' : runtimeStateMatchesIR fields runtime' state' :=
         runtimeStateMatchesIR_setVar_bindValue hruntime name valueNat
       have hexact' : bindingsExactlyMatchIRVars runtime'.bindings state' :=
         bindingsExactlyMatchIRVars_setVar_bindValue hexact name valueNat
       have hbounded' : bindingsBounded runtime'.bindings :=
         bindingsBounded_bindValue hbounded name valueNat hvalueLt
       have hscope' : scopeNamesPresent (name :: scope) runtime'.bindings :=
         scopeNamesPresent_cons_bindValue hscope
       rcases ih (runtime := runtime') (state := state')
           (inScopeNames := collectStmtNames (.letVar name value) ++ inScopeNames)
           hscope' hexact' hbounded' hruntime' with
         ⟨tailIR, htailCompile, htailSem, htailExact⟩
       refine ⟨[YulStmt.let_ name valueIR] ++ tailIR, ?_, ?_⟩
       · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
         rw [hvalueIR]
         simp [htailCompile]
         exact rfl
       · have hstmt :
             execIRStmt (tailIR.length + 1) state (YulStmt.let_ name valueIR) =
               .continue state' := by
           simp [execIRStmt, heval', state', valueNat]
         have hirExec :
             execIRStmts (tailIR.length + 2) state
               (YulStmt.let_ name valueIR :: tailIR) =
               execIRStmts (tailIR.length + 1) state' tailIR := by
           simpa using
             (execIRStmts_cons_of_execIRStmt_continue state state'
               (YulStmt.let_ name valueIR) tailIR hstmt)
         rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
         dsimp [runtime', state']
         constructor
         · simpa [hirExec, runtime', valueNat] using htailSem
         · simpa [hirExec, runtime', valueNat] using htailExact
   | assignVar hvalue hinScope hrest ih =>
       rename_i scope name value rest
       have hpresent : exprBoundNamesPresent value runtime.bindings :=
         exprBoundNamesPresent_of_scope hscope hinScope
       rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
       let valueNat := SourceSemantics.evalExpr fields runtime value
       let runtime' :=
         { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
       let state' := state.setVar name valueNat
       have heval := eval_compileExpr_core hvalue hexact hbounded hpresent hruntime
       rw [hvalueIR] at heval
       have heval' : evalIRExpr state valueIR = some valueNat := by
         simpa [valueNat] using heval
       have hvalueLt := evalExpr_lt_evmModulus_core hvalue hexact hbounded hpresent hruntime
       have hruntime' : runtimeStateMatchesIR fields runtime' state' :=
         runtimeStateMatchesIR_setVar_bindValue hruntime name valueNat
       have hexact' : bindingsExactlyMatchIRVars runtime'.bindings state' :=
         bindingsExactlyMatchIRVars_setVar_bindValue hexact name valueNat
       have hbounded' : bindingsBounded runtime'.bindings :=
         bindingsBounded_bindValue hbounded name valueNat hvalueLt
       have hscope' : scopeNamesPresent (name :: scope) runtime'.bindings :=
         scopeNamesPresent_cons_bindValue hscope
       rcases ih (runtime := runtime') (state := state')
           (inScopeNames := collectStmtNames (.assignVar name value) ++ inScopeNames)
           hscope' hexact' hbounded' hruntime' with
         ⟨tailIR, htailCompile, htailSem, htailExact⟩
       refine ⟨[YulStmt.assign name valueIR] ++ tailIR, ?_, ?_⟩
       · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
         rw [hvalueIR]
         simp [htailCompile]
         exact rfl
       · have hstmt :
             execIRStmt (tailIR.length + 1) state (YulStmt.assign name valueIR) =
               .continue state' := by
           simp [execIRStmt, heval', state', valueNat]
         have hirExec :
             execIRStmts (tailIR.length + 2) state
               (YulStmt.assign name valueIR :: tailIR) =
               execIRStmts (tailIR.length + 1) state' tailIR := by
           simpa using
             (execIRStmts_cons_of_execIRStmt_continue state state'
               (YulStmt.assign name valueIR) tailIR hstmt)
         rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
         dsimp [runtime', state']
         constructor
         · simpa [hirExec, runtime', valueNat] using htailSem
         · simpa [hirExec, runtime', valueNat] using htailExact
   | require_ hcond hinScope hrest ih =>
       rename_i scope cond message rest
       have hpresent : exprBoundNamesPresent cond runtime.bindings :=
         exprBoundNamesPresent_of_scope hscope hinScope
       rcases eval_compileRequireFailCond_core hcond hexact hbounded hpresent hruntime with
         ⟨failCond, hfailCompile, hfailEval⟩
       rcases ih (runtime := runtime) (state := state)
           (inScopeNames := collectStmtNames (.require cond message) ++ inScopeNames)
           hscope hexact hbounded hruntime with
         ⟨tailIR, htailCompile, htailSem, htailExact⟩
       refine ⟨[YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR, ?_, ?_⟩
       · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
         rw [hfailCompile]
         simp [htailCompile]
         exact rfl
       · by_cases hcondZero : SourceSemantics.evalExpr fields runtime cond = 0
         · rcases execIRStmts_revertWithMessage_revert (fuel := tailIR.length) (state := state) message with
             ⟨revState, hrev⟩
           have hfailEval' : evalIRExpr state failCond = some 1 := by
             simpa [hcondZero, SourceSemantics.boolWord] using hfailEval
           have hstmt :
               execIRStmt (tailIR.length + 1) state
                 (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) =
                   .revert revState := by
             simp [execIRStmt, hfailEval', hrev]
           have hirExec :
               execIRStmts (tailIR.length + 2) state
                 (YulStmt.if_ failCond (CompilationModel.revertWithMessage message) :: tailIR) =
                   .revert revState := by
             simpa using
               (execIRStmts_cons_of_execIRStmt_revert state revState
                 (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) tailIR hstmt)
           rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
           simp [hcondZero, hirExec, stmtResultMatchesIRExec, stmtResultMatchesIRExecExact]
         · have hfailEval' : evalIRExpr state failCond = some 0 := by
             simpa [hcondZero, SourceSemantics.boolWord] using hfailEval
           have hstmt :
               execIRStmt (tailIR.length + 1) state
                 (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) =
                   .continue state := by
             simp [execIRStmt, hfailEval']
           have hirExec :
               execIRStmts (tailIR.length + 2) state
                 (YulStmt.if_ failCond (CompilationModel.revertWithMessage message) :: tailIR) =
                   execIRStmts (tailIR.length + 1) state tailIR := by
             simpa using
               (execIRStmts_cons_of_execIRStmt_continue state state
                 (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) tailIR hstmt)
           rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
           simp [hcondZero, hirExec]
           constructor
           · simpa [hirExec] using htailSem
           · simpa [hirExec] using htailExact
   | return_ hvalue hinScope hrest ih =>
       rename_i scope value rest
       have hpresent : exprBoundNamesPresent value runtime.bindings :=
         exprBoundNamesPresent_of_scope hscope hinScope
       rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
       let retVal := SourceSemantics.evalExpr fields runtime value
       let state' := { state with memory := fun o => if o = 0 then retVal else state.memory o }
       rcases ih (runtime := runtime) (state := state')
           (inScopeNames := collectStmtNames (.return value) ++ inScopeNames)
           hscope
           (bindingsExactlyMatchIRVars_setMemory hexact 0 retVal)
           hbounded
           (runtimeStateMatchesIR_setMemory hruntime 0 retVal) with
         ⟨tailIR, htailCompile, htailSem, htailExact⟩
       refine ⟨[ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
               , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++ tailIR,
         ?_, ?_⟩
       · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
         rw [hvalueIR]
         simp [htailCompile]
         exact rfl
       · have heval := eval_compileExpr_core hvalue hexact hbounded hpresent hruntime
         rw [hvalueIR] at heval
         have heval' : evalIRExpr state valueIR = some retVal := by
           simpa [retVal] using heval
         have hruntime' : runtimeStateMatchesIR fields runtime state' :=
           runtimeStateMatchesIR_setMemory hruntime 0 retVal
         have hexact' : bindingsExactlyMatchIRVars runtime.bindings state' :=
           bindingsExactlyMatchIRVars_setMemory hexact 0 retVal
         have hmstore :
             execIRStmt (tailIR.length + 2) state
               (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])) =
               .continue state' := by
           simp [execIRStmt, evalIRExpr, heval', retVal, state']
         have hreturn :
             execIRStmt (tailIR.length + 1) state'
               (YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])) =
               .return retVal state' := by
           simp [execIRStmt, evalIRExpr, retVal, state']
         have hirExec :
             execIRStmts (tailIR.length + 3)
               state
               (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR]) ::
                 YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ::
                 tailIR) =
               .return retVal state' := by
           simpa using
             (execIRStmts_two_of_continue_then_return state state' state'
               (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR]))
               (YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]))
               tailIR retVal hmstore hreturn)
         rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
         dsimp [retVal, state']
         constructor
         · simpa [hirExec] using (show
             stmtResultMatchesIRExec fields
               (SourceSemantics.StmtResult.return retVal runtime)
               (.return retVal state') from ⟨rfl, hruntime'⟩)
         · simpa [hirExec] using (show
             stmtResultMatchesIRExecExact
               (SourceSemantics.StmtResult.return retVal runtime)
               (.return retVal state') from ⟨hexact', hbounded⟩)
   | stop hrest ih =>
       rename_i scope rest
       rcases ih (runtime := runtime) (state := state)
           (inScopeNames := collectStmtNames (.stop) ++ inScopeNames)
           hscope hexact hbounded hruntime with
         ⟨tailIR, htailCompile, htailSem, htailExact⟩
       refine ⟨[YulStmt.expr (YulExpr.call "stop" [])] ++ tailIR, ?_, ?_⟩
       · simpa [CompilationModel.compileStmtList, CompilationModel.compileStmt, htailCompile]
       · have hstmt :
             execIRStmt (tailIR.length + 1) state (YulStmt.expr (YulExpr.call "stop" [])) =
               .stop state := by
           simp [execIRStmt]
         have hirExec :
             execIRStmts (tailIR.length + 2) state
               (YulStmt.expr (YulExpr.call "stop" []) :: tailIR) =
               .stop state := by
           simpa using
             (execIRStmts_cons_of_execIRStmt_stop state state
               (YulStmt.expr (YulExpr.call "stop" [])) tailIR hstmt)
         rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
         simp [hirExec]
         exact ⟨hruntime, ⟨hexact, hbounded⟩⟩

theorem exec_compileStmtList_core_extraFuel
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope inScopeNames : List String}
    {stmts : List Stmt}
    (extraFuel : Nat)
    (hcore : StmtListCompileCore scope stmts)
    (hscope : scopeNamesPresent scope runtime.bindings)
    (hexact : bindingsExactlyMatchIRVars runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames stmts = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmtList fields runtime stmts
      let irExec := execIRStmts (bodyIR.length + extraFuel + 1) state bodyIR
      stmtResultMatchesIRExec fields sourceResult irExec ∧
      stmtResultMatchesIRExecExact sourceResult irExec := by
   induction hcore generalizing runtime state inScopeNames with
   | nil =>
       refine ⟨[], rfl, ?_⟩
       constructor
       · simpa [SourceSemantics.execStmtList, execIRStmts, stmtResultMatchesIRExec] using hruntime
       · simpa [SourceSemantics.execStmtList, execIRStmts, stmtResultMatchesIRExecExact] using
           And.intro hexact hbounded
   | letVar hvalue hinScope hrest ih =>
       rename_i scope name value rest
       have hpresent : exprBoundNamesPresent value runtime.bindings :=
         exprBoundNamesPresent_of_scope hscope hinScope
       rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
       let valueNat := SourceSemantics.evalExpr fields runtime value
       let runtime' :=
         { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
       let state' := state.setVar name valueNat
       have heval := eval_compileExpr_core hvalue hexact hbounded hpresent hruntime
       rw [hvalueIR] at heval
       have heval' : evalIRExpr state valueIR = some valueNat := by
         simpa [valueNat] using heval
       have hvalueLt := evalExpr_lt_evmModulus_core hvalue hexact hbounded hpresent hruntime
       have hruntime' : runtimeStateMatchesIR fields runtime' state' :=
         runtimeStateMatchesIR_setVar_bindValue hruntime name valueNat
       have hexact' : bindingsExactlyMatchIRVars runtime'.bindings state' :=
         bindingsExactlyMatchIRVars_setVar_bindValue hexact name valueNat
       have hbounded' : bindingsBounded runtime'.bindings :=
         bindingsBounded_bindValue hbounded name valueNat hvalueLt
       have hscope' : scopeNamesPresent (name :: scope) runtime'.bindings :=
         scopeNamesPresent_cons_bindValue hscope
       rcases ih (runtime := runtime') (state := state')
           (inScopeNames := collectStmtNames (.letVar name value) ++ inScopeNames)
           hscope' hexact' hbounded' hruntime' with
         ⟨tailIR, htailCompile, htailSem, htailExact⟩
       refine ⟨[YulStmt.let_ name valueIR] ++ tailIR, ?_, ?_⟩
       · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
         rw [hvalueIR]
         simp [htailCompile]
         exact rfl
       · have hstmt :
             execIRStmt (tailIR.length + extraFuel + 1) state (YulStmt.let_ name valueIR) =
               .continue state' := by
           simp [execIRStmt, heval', state', valueNat]
         have hirExec :
             execIRStmts (tailIR.length + extraFuel + 2) state
               (YulStmt.let_ name valueIR :: tailIR) =
               execIRStmts (tailIR.length + extraFuel + 1) state' tailIR := by
           simpa using
             (execIRStmts_cons_of_execIRStmt_continue_extraFuel extraFuel state state'
               (YulStmt.let_ name valueIR) tailIR hstmt)
         rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
         dsimp [runtime', state']
         constructor
         · have hirExec' :
               execIRStmts (tailIR.length + 1 + extraFuel + 1) state
                 (YulStmt.let_ name valueIR :: tailIR) =
                 execIRStmts (tailIR.length + extraFuel + 1) state' tailIR := by
             simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hirExec
           rw [hirExec']
           simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, runtime', valueNat] using htailSem
         · have hirExec' :
               execIRStmts (tailIR.length + 1 + extraFuel + 1) state
                 (YulStmt.let_ name valueIR :: tailIR) =
                 execIRStmts (tailIR.length + extraFuel + 1) state' tailIR := by
             simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hirExec
           rw [hirExec']
           simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, runtime', valueNat] using htailExact
   | assignVar hvalue hinScope hrest ih =>
       rename_i scope name value rest
       have hpresent : exprBoundNamesPresent value runtime.bindings :=
         exprBoundNamesPresent_of_scope hscope hinScope
       rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
       let valueNat := SourceSemantics.evalExpr fields runtime value
       let runtime' :=
         { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
       let state' := state.setVar name valueNat
       have heval := eval_compileExpr_core hvalue hexact hbounded hpresent hruntime
       rw [hvalueIR] at heval
       have heval' : evalIRExpr state valueIR = some valueNat := by
         simpa [valueNat] using heval
       have hvalueLt := evalExpr_lt_evmModulus_core hvalue hexact hbounded hpresent hruntime
       have hruntime' : runtimeStateMatchesIR fields runtime' state' :=
         runtimeStateMatchesIR_setVar_bindValue hruntime name valueNat
       have hexact' : bindingsExactlyMatchIRVars runtime'.bindings state' :=
         bindingsExactlyMatchIRVars_setVar_bindValue hexact name valueNat
       have hbounded' : bindingsBounded runtime'.bindings :=
         bindingsBounded_bindValue hbounded name valueNat hvalueLt
       have hscope' : scopeNamesPresent (name :: scope) runtime'.bindings :=
         scopeNamesPresent_cons_bindValue hscope
       rcases ih (runtime := runtime') (state := state')
           (inScopeNames := collectStmtNames (.assignVar name value) ++ inScopeNames)
           hscope' hexact' hbounded' hruntime' with
         ⟨tailIR, htailCompile, htailSem, htailExact⟩
       refine ⟨[YulStmt.assign name valueIR] ++ tailIR, ?_, ?_⟩
       · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
         rw [hvalueIR]
         simp [htailCompile]
         exact rfl
       · have hstmt :
             execIRStmt (tailIR.length + extraFuel + 1) state (YulStmt.assign name valueIR) =
               .continue state' := by
           simp [execIRStmt, heval', state', valueNat]
         have hirExec :
             execIRStmts (tailIR.length + extraFuel + 2) state
               (YulStmt.assign name valueIR :: tailIR) =
               execIRStmts (tailIR.length + extraFuel + 1) state' tailIR := by
           simpa using
             (execIRStmts_cons_of_execIRStmt_continue_extraFuel extraFuel state state'
               (YulStmt.assign name valueIR) tailIR hstmt)
         rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
         dsimp [runtime', state']
         constructor
         · have hirExec' :
               execIRStmts (tailIR.length + 1 + extraFuel + 1) state
                 (YulStmt.assign name valueIR :: tailIR) =
                 execIRStmts (tailIR.length + extraFuel + 1) state' tailIR := by
             simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hirExec
           rw [hirExec']
           simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, runtime', valueNat] using htailSem
         · have hirExec' :
               execIRStmts (tailIR.length + 1 + extraFuel + 1) state
                 (YulStmt.assign name valueIR :: tailIR) =
                 execIRStmts (tailIR.length + extraFuel + 1) state' tailIR := by
             simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hirExec
           rw [hirExec']
           simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, runtime', valueNat] using htailExact
   | require_ hcond hinScope hrest ih =>
       rename_i scope cond message rest
       have hpresent : exprBoundNamesPresent cond runtime.bindings :=
         exprBoundNamesPresent_of_scope hscope hinScope
       rcases eval_compileRequireFailCond_core hcond hexact hbounded hpresent hruntime with
         ⟨failCond, hfailCompile, hfailEval⟩
       rcases ih (runtime := runtime) (state := state)
           (inScopeNames := collectStmtNames (.require cond message) ++ inScopeNames)
           hscope hexact hbounded hruntime with
         ⟨tailIR, htailCompile, htailSem, htailExact⟩
       refine ⟨[YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR, ?_, ?_⟩
       · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
         rw [hfailCompile]
         simp [htailCompile]
         exact rfl
       · by_cases hcondZero : SourceSemantics.evalExpr fields runtime cond = 0
         · rcases execIRStmts_revertWithMessage_revert (fuel := tailIR.length + extraFuel)
             (state := state) message with
             ⟨revState, hrev⟩
           have hfailEval' : evalIRExpr state failCond = some 1 := by
             simpa [hcondZero, SourceSemantics.boolWord] using hfailEval
           have hstmt :
               execIRStmt (tailIR.length + extraFuel + 1) state
                 (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) =
                   .revert revState := by
             simp [execIRStmt, hfailEval', hrev]
           have hirExec :
               execIRStmts (tailIR.length + extraFuel + 2) state
                 (YulStmt.if_ failCond (CompilationModel.revertWithMessage message) :: tailIR) =
                   .revert revState := by
             simpa using
               (execIRStmts_cons_of_execIRStmt_revert_extraFuel extraFuel state revState
                 (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) tailIR hstmt)
           have hirExec' :
               execIRStmts (tailIR.length + 1 + extraFuel + 1) state
                 (YulStmt.if_ failCond (CompilationModel.revertWithMessage message) :: tailIR) =
                   .revert revState := by
             simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hirExec
           rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
           simp [hcondZero, hirExec', stmtResultMatchesIRExec, stmtResultMatchesIRExecExact]
         · have hfailEval' : evalIRExpr state failCond = some 0 := by
             simpa [hcondZero, SourceSemantics.boolWord] using hfailEval
           have hstmt :
               execIRStmt (tailIR.length + extraFuel + 1) state
                 (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) =
                   .continue state := by
             simp [execIRStmt, hfailEval']
           have hirExec :
               execIRStmts (tailIR.length + extraFuel + 2) state
                 (YulStmt.if_ failCond (CompilationModel.revertWithMessage message) :: tailIR) =
                   execIRStmts (tailIR.length + extraFuel + 1) state tailIR := by
             simpa using
               (execIRStmts_cons_of_execIRStmt_continue_extraFuel extraFuel state state
                 (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) tailIR hstmt)
           have hirExec' :
               execIRStmts (tailIR.length + 1 + extraFuel + 1) state
                 (YulStmt.if_ failCond (CompilationModel.revertWithMessage message) :: tailIR) =
                   execIRStmts (tailIR.length + extraFuel + 1) state tailIR := by
             simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hirExec
           rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
           simp [hcondZero, hirExec']
           constructor
           · exact htailSem
           · exact htailExact
   | return_ hvalue hinScope hrest ih =>
       rename_i scope value rest
       have hpresent : exprBoundNamesPresent value runtime.bindings :=
         exprBoundNamesPresent_of_scope hscope hinScope
       rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
       let retVal := SourceSemantics.evalExpr fields runtime value
       let state' := { state with memory := fun o => if o = 0 then retVal else state.memory o }
       rcases ih (runtime := runtime) (state := state')
           (inScopeNames := collectStmtNames (.return value) ++ inScopeNames)
           hscope
           (bindingsExactlyMatchIRVars_setMemory hexact 0 retVal)
           hbounded
           (runtimeStateMatchesIR_setMemory hruntime 0 retVal) with
         ⟨tailIR, htailCompile, htailSem, htailExact⟩
       refine ⟨[ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
               , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++ tailIR,
         ?_, ?_⟩
       · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
         rw [hvalueIR]
         simp [htailCompile]
         exact rfl
       · have heval := eval_compileExpr_core hvalue hexact hbounded hpresent hruntime
         rw [hvalueIR] at heval
         have heval' : evalIRExpr state valueIR = some retVal := by
           simpa [retVal] using heval
         have hruntime' : runtimeStateMatchesIR fields runtime state' :=
           runtimeStateMatchesIR_setMemory hruntime 0 retVal
         have hexact' : bindingsExactlyMatchIRVars runtime.bindings state' :=
           bindingsExactlyMatchIRVars_setMemory hexact 0 retVal
         have hmstore :
             execIRStmt (tailIR.length + extraFuel + 2) state
               (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])) =
               .continue state' := by
           simp [execIRStmt, evalIRExpr, heval', retVal, state']
         have hreturn :
             execIRStmt (tailIR.length + extraFuel + 1) state'
               (YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])) =
               .return retVal state' := by
           simp [execIRStmt, evalIRExpr, retVal, state']
         have hirExec :
             execIRStmts (tailIR.length + extraFuel + 3)
               state
               (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR]) ::
                 YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ::
                 tailIR) =
               .return retVal state' := by
           simpa using
             (execIRStmts_two_of_continue_then_return_extraFuel extraFuel state state' state'
               (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR]))
               (YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]))
               tailIR retVal hmstore hreturn)
         have hirExec' :
             execIRStmts (tailIR.length + 1 + 1 + extraFuel + 1)
               state
               (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR]) ::
                 YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ::
                 tailIR) =
               .return retVal state' := by
           simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hirExec
         rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
         dsimp [retVal, state']
         constructor
         · rw [hirExec']
           simpa using (show
             stmtResultMatchesIRExec fields
               (SourceSemantics.StmtResult.return retVal runtime)
               (.return retVal state') from ⟨rfl, hruntime'⟩)
         · rw [hirExec']
           simpa using (show
             stmtResultMatchesIRExecExact
               (SourceSemantics.StmtResult.return retVal runtime)
               (.return retVal state') from ⟨hexact', hbounded⟩)
   | stop hrest ih =>
       rename_i scope rest
       rcases ih (runtime := runtime) (state := state)
           (inScopeNames := collectStmtNames (.stop) ++ inScopeNames)
           hscope hexact hbounded hruntime with
         ⟨tailIR, htailCompile, htailSem, htailExact⟩
       refine ⟨[YulStmt.expr (YulExpr.call "stop" [])] ++ tailIR, ?_, ?_⟩
       · simpa [CompilationModel.compileStmtList, CompilationModel.compileStmt, htailCompile]
       · have hstmt :
             execIRStmt (tailIR.length + extraFuel + 1) state
               (YulStmt.expr (YulExpr.call "stop" [])) =
               .stop state := by
           simp [execIRStmt]
         have hirExec :
             execIRStmts (tailIR.length + extraFuel + 2) state
               (YulStmt.expr (YulExpr.call "stop" []) :: tailIR) =
               .stop state := by
           simpa using
             (execIRStmts_cons_of_execIRStmt_stop_extraFuel extraFuel state state
               (YulStmt.expr (YulExpr.call "stop" [])) tailIR hstmt)
         have hirExec' :
             execIRStmts (tailIR.length + 1 + extraFuel + 1) state
               (YulStmt.expr (YulExpr.call "stop" []) :: tailIR) =
               .stop state := by
           simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hirExec
         rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
         simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, hirExec'] using
           (show stmtResultMatchesIRExec fields (SourceSemantics.StmtResult.stop runtime) (.stop state) ∧
               stmtResultMatchesIRExecExact (SourceSemantics.StmtResult.stop runtime) (.stop state) from
             ⟨hruntime, ⟨hexact, hbounded⟩⟩)

private theorem compiled_terminal_ite_body_block_extraFuel_eq
    (extraFuel : Nat)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt) :
    sizeOf
        ([YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_
                (YulExpr.call "iszero" [YulExpr.ident tempName])
                elseIR
            ]] ++ tailIR) + extraFuel - 1 =
      sizeOf
        [ YulStmt.let_ tempName condIR
        , YulStmt.if_ (YulExpr.ident tempName) thenIR
        , YulStmt.if_
            (YulExpr.call "iszero" [YulExpr.ident tempName])
            elseIR ] +
        (sizeOf
          ([YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_
                  (YulExpr.call "iszero" [YulExpr.ident tempName])
                  elseIR
              ]] ++ tailIR) -
          (sizeOf
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_
                (YulExpr.call "iszero" [YulExpr.ident tempName])
                elseIR ] + 2) +
          extraFuel) + 1 := by
  have hblock :=
    compiled_terminal_ite_body_size_ge_blockFuel tempName condIR thenIR elseIR tailIR
  omega

private theorem compiled_terminal_ite_body_thenBranch_extraFuel_eq
    (extraFuel : Nat)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt) :
    sizeOf
        ([YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_
                (YulExpr.call "iszero" [YulExpr.ident tempName])
                elseIR
            ]] ++ tailIR) + extraFuel - 4 =
      sizeOf thenIR +
        (sizeOf
          ([YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_
                  (YulExpr.call "iszero" [YulExpr.ident tempName])
                  elseIR
              ]] ++ tailIR) -
          (sizeOf thenIR + 5) +
          extraFuel) + 1 := by
  have hbranch :=
    (compiled_terminal_ite_body_size_ge_branchExecFuel tempName condIR thenIR elseIR tailIR).1
  omega

private theorem compiled_terminal_ite_body_elseBranch_extraFuel_eq
    (extraFuel : Nat)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt) :
    sizeOf
        ([YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_
                (YulExpr.call "iszero" [YulExpr.ident tempName])
                elseIR
            ]] ++ tailIR) + extraFuel - 4 =
      sizeOf elseIR +
        (sizeOf
          ([YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_
                  (YulExpr.call "iszero" [YulExpr.ident tempName])
                  elseIR
              ]] ++ tailIR) -
          (sizeOf elseIR + 5) +
          extraFuel) + 1 := by
  have hbranch :=
    (compiled_terminal_ite_body_size_ge_branchExecFuel tempName condIR thenIR elseIR tailIR).2
  omega

private theorem compiled_terminal_ite_body_thenBranch_execFuel_eq
    (extraFuel : Nat)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt) :
    sizeOf thenIR +
        (sizeOf
          ([YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_
                  (YulExpr.call "iszero" [YulExpr.ident tempName])
                  elseIR
              ]] ++ tailIR) -
          (sizeOf thenIR + 5) +
          extraFuel) + 1 =
      sizeOf
        ([YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_
                (YulExpr.call "iszero" [YulExpr.ident tempName])
                elseIR
            ]] ++ tailIR) + extraFuel - 4 := by
  simpa using
    (compiled_terminal_ite_body_thenBranch_extraFuel_eq
      extraFuel tempName condIR thenIR elseIR tailIR).symm

private theorem compiled_terminal_ite_body_thenBranch_tailExecFuel_eq
    (extraFuel : Nat)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt) :
    sizeOf thenIR +
        (sizeOf
          ([YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_
                  (YulExpr.call "iszero" [YulExpr.ident tempName])
                  elseIR
              ]] ++ tailIR) -
          (sizeOf thenIR + 5) +
          extraFuel) =
      sizeOf
        ([YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_
                (YulExpr.call "iszero" [YulExpr.ident tempName])
                elseIR
            ]] ++ tailIR) + extraFuel - 5 := by
  have hbranch :=
    (compiled_terminal_ite_body_size_ge_branchExecFuel tempName condIR thenIR elseIR tailIR).1
  omega

private theorem compiled_terminal_ite_body_elseBranch_execFuel_eq
    (extraFuel : Nat)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt) :
    sizeOf elseIR +
        (sizeOf
          ([YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_
                  (YulExpr.call "iszero" [YulExpr.ident tempName])
                  elseIR
              ]] ++ tailIR) -
          (sizeOf elseIR + 5) +
          extraFuel) + 1 =
      sizeOf
        ([YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_
                (YulExpr.call "iszero" [YulExpr.ident tempName])
                elseIR
            ]] ++ tailIR) + extraFuel - 4 := by
  simpa using
    (compiled_terminal_ite_body_elseBranch_extraFuel_eq
      extraFuel tempName condIR thenIR elseIR tailIR).symm

private theorem compiled_terminal_ite_body_elseBranch_tailExecFuel_eq
    (extraFuel : Nat)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt) :
    sizeOf elseIR +
        (sizeOf
          ([YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_
                  (YulExpr.call "iszero" [YulExpr.ident tempName])
                  elseIR
              ]] ++ tailIR) -
          (sizeOf elseIR + 5) +
          extraFuel) =
      sizeOf
        ([YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_
                (YulExpr.call "iszero" [YulExpr.ident tempName])
                elseIR
            ]] ++ tailIR) + extraFuel - 5 := by
  have hbranch :=
    (compiled_terminal_ite_body_size_ge_branchExecFuel tempName condIR thenIR elseIR tailIR).2
  omega

private theorem compiled_terminal_ite_body_letFuel_ne_zero
    (extraFuel : Nat)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt) :
    sizeOf
      ([YulStmt.block
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_
              (YulExpr.call "iszero" [YulExpr.ident tempName])
              elseIR
          ]] ++ tailIR) + extraFuel - 2 ≠ 0 := by
  have hbranch :=
    (compiled_terminal_ite_body_size_ge_branchExecFuel tempName condIR thenIR elseIR tailIR).1
  omega

private theorem compiled_terminal_ite_body_thenIfFuel_ne_zero
    (extraFuel : Nat)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt) :
    sizeOf
      ([YulStmt.block
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_
              (YulExpr.call "iszero" [YulExpr.ident tempName])
              elseIR
          ]] ++ tailIR) + extraFuel - 3 ≠ 0 := by
  have hbranch :=
    (compiled_terminal_ite_body_size_ge_branchExecFuel tempName condIR thenIR elseIR tailIR).1
  omega

private theorem compiled_terminal_ite_body_elseIfFuel_ne_zero
    (extraFuel : Nat)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt) :
    sizeOf
      ([YulStmt.block
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_
              (YulExpr.call "iszero" [YulExpr.ident tempName])
              elseIR
          ]] ++ tailIR) + extraFuel - 4 ≠ 0 := by
  have hbranch :=
    (compiled_terminal_ite_body_size_ge_branchExecFuel tempName condIR thenIR elseIR tailIR).2
  omega

private theorem compiled_terminal_ite_body_blockStmtFuel_ne_zero
    (extraFuel : Nat)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt) :
    sizeOf
      ([YulStmt.block
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_
              (YulExpr.call "iszero" [YulExpr.ident tempName])
              elseIR
          ]] ++ tailIR) + extraFuel ≠ 0 := by
  have hblock :=
    compiled_terminal_ite_body_size_ge_blockFuel tempName condIR thenIR elseIR tailIR
  omega

private theorem compiled_terminal_ite_body_block_execFuel_eq
    (extraFuel : Nat)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt) :
    sizeOf
        [ YulStmt.let_ tempName condIR
        , YulStmt.if_ (YulExpr.ident tempName) thenIR
        , YulStmt.if_
            (YulExpr.call "iszero" [YulExpr.ident tempName])
            elseIR ] +
      (sizeOf
          ([YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_
                  (YulExpr.call "iszero" [YulExpr.ident tempName])
                  elseIR
              ]] ++ tailIR) -
        (sizeOf
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_
              (YulExpr.call "iszero" [YulExpr.ident tempName])
              elseIR ] + 2) +
        extraFuel) + 1 =
      sizeOf
        ([YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_
                (YulExpr.call "iszero" [YulExpr.ident tempName])
                elseIR
            ]] ++ tailIR) + extraFuel - 1 := by
  simpa using
    (compiled_terminal_ite_body_block_extraFuel_eq
      extraFuel tempName condIR thenIR elseIR tailIR).symm

private theorem execIRStmt_compiled_terminal_ite_let
    (extraFuel : Nat)
    (state : IRState)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt)
    (condValue : Nat)
    (hcond : evalIRExpr state condIR = some condValue) :
    execIRStmt
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 2)
        state
        (YulStmt.let_ tempName condIR) =
      .continue (state.setVar tempName condValue) := by
  simpa using
    execIRStmt_let_of_eval_nonzeroFuel
      (fuel :=
        sizeOf
          ([YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_
                  (YulExpr.call "iszero" [YulExpr.ident tempName])
                  elseIR
              ]] ++ tailIR) + extraFuel - 2)
      (state := state)
      (name := tempName)
      (valueExpr := condIR)
      (value := condValue)
      (compiled_terminal_ite_body_letFuel_ne_zero extraFuel tempName condIR thenIR elseIR tailIR)
      hcond

private theorem evalIRExpr_compiled_terminal_ite_elseCond_of_zero
    (state : IRState)
    (tempName : String)
    (condValue : Nat)
    (hcondZero : condValue = 0) :
    evalIRExpr (state.setVar tempName condValue)
      (YulExpr.call "iszero" [YulExpr.ident tempName]) = some 1 := by
  simp [evalIRExpr, evalIRCall, evalIRExprs, hcondZero,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext]

/-- Entering the taken `then` branch of a compiled terminal `ite` re-expresses
the remaining fuel in the branch-local schema expected by recursive body
simulation proofs. -/
theorem execIRStmt_compiled_terminal_ite_then_branch_entry
    (extraFuel : Nat)
    (state : IRState)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt)
    (condValue : Nat)
    (hcondNonzero : condValue ≠ 0) :
    execIRStmt
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 3)
        (state.setVar tempName condValue)
        (YulStmt.if_ (YulExpr.ident tempName) thenIR) =
      execIRStmts
        (sizeOf thenIR +
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) -
            (sizeOf thenIR + 5) +
            extraFuel) + 1)
        (state.setVar tempName condValue) thenIR := by
  have hident :
      evalIRExpr (state.setVar tempName condValue) (YulExpr.ident tempName) = some condValue := by
    simp [evalIRExpr]
  have hstep :
      execIRStmt
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel - 3)
          (state.setVar tempName condValue)
          (YulStmt.if_ (YulExpr.ident tempName) thenIR) =
        execIRStmts
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel - 4)
          (state.setVar tempName condValue) thenIR := by
    simpa using
      execIRStmt_if_true_of_eval_nonzeroFuel
        (fuel :=
          sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 3)
        (state := state.setVar tempName condValue)
        (cond := YulExpr.ident tempName)
        (body := thenIR)
        (value := condValue)
        (compiled_terminal_ite_body_thenIfFuel_ne_zero extraFuel tempName condIR thenIR elseIR tailIR)
        hident
        hcondNonzero
  have hfuelEq :
      sizeOf
          ([YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_
                  (YulExpr.call "iszero" [YulExpr.ident tempName])
                  elseIR
              ]] ++ tailIR) + extraFuel - 4 =
        sizeOf thenIR +
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) -
            (sizeOf thenIR + 5) +
            extraFuel) + 1 := by
    simpa using
      (compiled_terminal_ite_body_thenBranch_execFuel_eq
        extraFuel tempName condIR thenIR elseIR tailIR).symm
  calc
    execIRStmt
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 3)
        (state.setVar tempName condValue)
        (YulStmt.if_ (YulExpr.ident tempName) thenIR)
        =
      execIRStmts
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 4)
        (state.setVar tempName condValue) thenIR := hstep
    _ =
      execIRStmts
        (sizeOf thenIR +
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) -
            (sizeOf thenIR + 5) +
            extraFuel) + 1)
        (state.setVar tempName condValue) thenIR := by
          rw [hfuelEq]

private theorem execIRStmt_compiled_terminal_ite_thenIf_false
    (extraFuel : Nat)
    (state : IRState)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt)
    (condValue : Nat)
    (hcondZero : condValue = 0) :
    execIRStmt
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 3)
        (state.setVar tempName condValue)
        (YulStmt.if_ (YulExpr.ident tempName) thenIR) =
      .continue (state.setVar tempName condValue) := by
  have hident :
      evalIRExpr (state.setVar tempName condValue) (YulExpr.ident tempName) = some condValue := by
    simp [evalIRExpr]
  simpa using
    execIRStmt_if_false_of_eval_nonzeroFuel
      (fuel :=
        sizeOf
          ([YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_
                  (YulExpr.call "iszero" [YulExpr.ident tempName])
                  elseIR
              ]] ++ tailIR) + extraFuel - 3)
      (state := state.setVar tempName condValue)
      (cond := YulExpr.ident tempName)
      (body := thenIR)
      (value := condValue)
      (compiled_terminal_ite_body_thenIfFuel_ne_zero extraFuel tempName condIR thenIR elseIR tailIR)
      hident
      hcondZero

/-- Entering the taken `else` branch of a compiled terminal `ite` still has one
token available for the branch body itself, so the resulting branch-local fuel
keeps the trailing `+ 1`. -/
theorem execIRStmt_compiled_terminal_ite_else_branch_entry
    (extraFuel : Nat)
    (state : IRState)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt)
    (condValue : Nat)
    (hcondZero : condValue = 0) :
    execIRStmt
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 3)
        (state.setVar tempName condValue)
        (YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR) =
      execIRStmts
        (sizeOf elseIR +
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) -
            (sizeOf elseIR + 5) +
            extraFuel) + 1)
        (state.setVar tempName condValue) elseIR := by
  have hiszero :
      evalIRExpr (state.setVar tempName condValue)
        (YulExpr.call "iszero" [YulExpr.ident tempName]) = some 1 :=
    evalIRExpr_compiled_terminal_ite_elseCond_of_zero state tempName condValue hcondZero
  have hstep :
      execIRStmt
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel - 3)
          (state.setVar tempName condValue)
          (YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR) =
        execIRStmts
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel - 4)
          (state.setVar tempName condValue) elseIR := by
    simpa using
      execIRStmt_if_true_of_eval_nonzeroFuel
        (fuel :=
          sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 3)
        (state := state.setVar tempName condValue)
        (cond := YulExpr.call "iszero" [YulExpr.ident tempName])
        (body := elseIR)
        (value := 1)
        (compiled_terminal_ite_body_thenIfFuel_ne_zero extraFuel tempName condIR thenIR elseIR tailIR)
        hiszero
        (by decide)
  have hfuelEq :
      sizeOf
          ([YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_
                  (YulExpr.call "iszero" [YulExpr.ident tempName])
                  elseIR
              ]] ++ tailIR) + extraFuel - 4 =
        sizeOf elseIR +
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) -
            (sizeOf elseIR + 5) +
            extraFuel) + 1 := by
    simpa using
      (compiled_terminal_ite_body_elseBranch_execFuel_eq
        extraFuel tempName condIR thenIR elseIR tailIR).symm
  calc
    execIRStmt
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 3)
        (state.setVar tempName condValue)
        (YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR)
        =
      execIRStmts
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 4)
        (state.setVar tempName condValue) elseIR := hstep
    _ =
      execIRStmts
        (sizeOf elseIR +
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) -
            (sizeOf elseIR + 5) +
            extraFuel) + 1)
        (state.setVar tempName condValue) elseIR := by
          rw [hfuelEq]

/-- Entering the taken `else` branch after the outer `if` token has already been
spent re-expresses the remaining fuel in the smaller branch-local schema needed
by the Layer 2 terminal-body induction. -/
theorem execIRStmt_compiled_terminal_ite_else_branch_entry_tailFuel
    (extraFuel : Nat)
    (state : IRState)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt)
    (condValue : Nat)
    (hcondZero : condValue = 0) :
    execIRStmt
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 4)
        (state.setVar tempName condValue)
        (YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR) =
      execIRStmts
        (sizeOf elseIR +
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) -
            (sizeOf elseIR + 5) +
            extraFuel))
        (state.setVar tempName condValue) elseIR := by
  have hiszero :
      evalIRExpr (state.setVar tempName condValue)
        (YulExpr.call "iszero" [YulExpr.ident tempName]) = some 1 :=
    evalIRExpr_compiled_terminal_ite_elseCond_of_zero state tempName condValue hcondZero
  have hstep :
      execIRStmt
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel - 4)
          (state.setVar tempName condValue)
          (YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR) =
        execIRStmts
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel - 5)
          (state.setVar tempName condValue) elseIR := by
    simpa using
      execIRStmt_if_true_of_eval_nonzeroFuel
        (fuel :=
          sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 4)
        (state := state.setVar tempName condValue)
        (cond := YulExpr.call "iszero" [YulExpr.ident tempName])
        (body := elseIR)
        (value := 1)
        (compiled_terminal_ite_body_elseIfFuel_ne_zero extraFuel tempName condIR thenIR elseIR tailIR)
        hiszero
        (by decide)
  have hfuelEq :
      sizeOf
          ([YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_
                  (YulExpr.call "iszero" [YulExpr.ident tempName])
                  elseIR
              ]] ++ tailIR) + extraFuel - 5 =
        sizeOf elseIR +
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) -
            (sizeOf elseIR + 5) +
            extraFuel) := by
    simpa using
      (compiled_terminal_ite_body_elseBranch_tailExecFuel_eq
        extraFuel tempName condIR thenIR elseIR tailIR).symm
  calc
    execIRStmt
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 4)
        (state.setVar tempName condValue)
        (YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR)
        =
      execIRStmts
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 5)
        (state.setVar tempName condValue) elseIR := hstep
    _ =
      execIRStmts
        (sizeOf elseIR +
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) -
            (sizeOf elseIR + 5) +
            extraFuel))
        (state.setVar tempName condValue) elseIR := by
          rw [hfuelEq]

private theorem execIRStmts_compiled_terminal_ite_then_of_irExec
    (extraFuel : Nat)
    (state : IRState)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt)
    (condValue : Nat)
    (irExec : IRExecResult)
    (hcond : evalIRExpr state condIR = some condValue)
    (hcondNonzero : condValue ≠ 0)
    (hthenExec :
      execIRStmts
        (sizeOf thenIR +
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) -
            (sizeOf thenIR + 5) +
            extraFuel) + 1)
        (state.setVar tempName condValue) thenIR = irExec)
    (hirNoContinue : ∀ next, irExec ≠ .continue next) :
    execIRStmts
      (sizeOf
          ([YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_
                  (YulExpr.call "iszero" [YulExpr.ident tempName])
                  elseIR
              ]] ++ tailIR) + extraFuel + 1)
      state
      ([YulStmt.block
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_
              (YulExpr.call "iszero" [YulExpr.ident tempName])
              elseIR
          ]] ++ tailIR) = irExec := by
  have hlet :=
    execIRStmt_compiled_terminal_ite_let
      extraFuel state tempName condIR thenIR elseIR tailIR condValue hcond
  have hthenStmt :
      execIRStmt
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 3)
        (state.setVar tempName condValue)
        (YulStmt.if_ (YulExpr.ident tempName) thenIR) = irExec := by
    rw [execIRStmt_compiled_terminal_ite_then_branch_entry
      extraFuel state tempName condIR thenIR elseIR tailIR condValue hcondNonzero]
    exact hthenExec
  have hafterLet :
      execIRStmts
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 2)
        (state.setVar tempName condValue)
        [ YulStmt.if_ (YulExpr.ident tempName) thenIR
        , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ] = irExec := by
    have hfuelEq :
        sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 2 =
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel - 3) + 1 := by
      have hblock :=
        (compiled_terminal_ite_body_size_ge_branchExecFuel tempName condIR thenIR elseIR tailIR).1
      omega
    rw [hfuelEq]
    cases hir : irExec
    · rename_i next
      exact False.elim (hirNoContinue next hir)
    · rename_i value next
      have hthenStmt' :
          execIRStmt
            (sizeOf
                ([YulStmt.block
                    [ YulStmt.let_ tempName condIR
                    , YulStmt.if_ (YulExpr.ident tempName) thenIR
                    , YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR
                    ]] ++ tailIR) + extraFuel - 3)
            (state.setVar tempName condValue)
            (YulStmt.if_ (YulExpr.ident tempName) thenIR) =
            .return value next := by
        simpa [hir] using hthenStmt
      simpa [hir] using
          (execIRStmts_cons_of_execIRStmt_return_anyFuel
            (fuel :=
              sizeOf
                ([YulStmt.block
                    [ YulStmt.let_ tempName condIR
                    , YulStmt.if_ (YulExpr.ident tempName) thenIR
                    , YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR
                    ]] ++ tailIR) + extraFuel - 3)
            (state := state.setVar tempName condValue)
            (next := next)
            (stmt := YulStmt.if_ (YulExpr.ident tempName) thenIR)
            (rest := [YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR])
            (value := value)
            hthenStmt')
    · rename_i next
      have hthenStmt' :
          execIRStmt
            (sizeOf
                ([YulStmt.block
                    [ YulStmt.let_ tempName condIR
                    , YulStmt.if_ (YulExpr.ident tempName) thenIR
                    , YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR
                    ]] ++ tailIR) + extraFuel - 3)
            (state.setVar tempName condValue)
            (YulStmt.if_ (YulExpr.ident tempName) thenIR) =
            .stop next := by
        simpa [hir] using hthenStmt
      simpa [hir] using
          (execIRStmts_cons_of_execIRStmt_stop_anyFuel
            (fuel :=
              sizeOf
                ([YulStmt.block
                    [ YulStmt.let_ tempName condIR
                    , YulStmt.if_ (YulExpr.ident tempName) thenIR
                    , YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR
                    ]] ++ tailIR) + extraFuel - 3)
            (state := state.setVar tempName condValue)
            (next := next)
            (stmt := YulStmt.if_ (YulExpr.ident tempName) thenIR)
            (rest := [YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR])
            hthenStmt')
    · rename_i next
      have hthenStmt' :
          execIRStmt
            (sizeOf
                ([YulStmt.block
                    [ YulStmt.let_ tempName condIR
                    , YulStmt.if_ (YulExpr.ident tempName) thenIR
                    , YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR
                    ]] ++ tailIR) + extraFuel - 3)
            (state.setVar tempName condValue)
            (YulStmt.if_ (YulExpr.ident tempName) thenIR) =
            .revert next := by
        simpa [hir] using hthenStmt
      simpa [hir] using
          (execIRStmts_cons_of_execIRStmt_revert_anyFuel
            (fuel :=
              sizeOf
                ([YulStmt.block
                    [ YulStmt.let_ tempName condIR
                    , YulStmt.if_ (YulExpr.ident tempName) thenIR
                    , YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR
                    ]] ++ tailIR) + extraFuel - 3)
            (state := state.setVar tempName condValue)
            (next := next)
            (stmt := YulStmt.if_ (YulExpr.ident tempName) thenIR)
            (rest := [YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR])
            hthenStmt')
  have hinner :
      execIRStmts
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 1)
        state
        [ YulStmt.let_ tempName condIR
        , YulStmt.if_ (YulExpr.ident tempName) thenIR
        , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ] = irExec := by
    have hfuelEq :
        sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 1 =
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel - 2) + 1 := by
      have hblock :=
        (compiled_terminal_ite_body_size_ge_branchExecFuel tempName condIR thenIR elseIR tailIR).1
      omega
    rw [hfuelEq]
    rw [execIRStmts_cons_of_execIRStmt_continue_anyFuel
      (fuel :=
        sizeOf
          ([YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_
                  (YulExpr.call "iszero" [YulExpr.ident tempName])
                  elseIR
              ]] ++ tailIR) + extraFuel - 2)
      (state := state)
      (next := state.setVar tempName condValue)
      (stmt := YulStmt.let_ tempName condIR)
      (rest :=
        [ YulStmt.if_ (YulExpr.ident tempName) thenIR
        , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ])
      hlet]
    exact hafterLet
  have hblock :
      execIRStmt
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel)
        state
        (YulStmt.block
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]) = irExec := by
    cases hir : irExec
    · rename_i next
      exact False.elim (hirNoContinue next hir)
    · rename_i value next
      have hinner' : execIRStmts
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR
                  ]] ++ tailIR) + extraFuel - 1)
          state
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ] =
          .return value next := by
        simpa [hir] using hinner
      simpa [hir] using
          (execIRStmt_block_of_execIRStmts_return_nonzeroFuel
            (fuel :=
              sizeOf
                ([YulStmt.block
                    [ YulStmt.let_ tempName condIR
                    , YulStmt.if_ (YulExpr.ident tempName) thenIR
                    , YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR
                    ]] ++ tailIR) + extraFuel)
            (state := state)
            (next := next)
            (body :=
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ])
            (value := value)
            (compiled_terminal_ite_body_blockStmtFuel_ne_zero
              extraFuel tempName condIR thenIR elseIR tailIR)
            hinner')
    · rename_i next
      have hinner' : execIRStmts
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR
                  ]] ++ tailIR) + extraFuel - 1)
          state
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ] =
          .stop next := by
        simpa [hir] using hinner
      simpa [hir] using
          (execIRStmt_block_of_execIRStmts_stop_nonzeroFuel
            (fuel :=
              sizeOf
                ([YulStmt.block
                    [ YulStmt.let_ tempName condIR
                    , YulStmt.if_ (YulExpr.ident tempName) thenIR
                    , YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR
                    ]] ++ tailIR) + extraFuel)
            (state := state)
            (next := next)
            (body :=
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ])
            (compiled_terminal_ite_body_blockStmtFuel_ne_zero
              extraFuel tempName condIR thenIR elseIR tailIR)
            hinner')
    · rename_i next
      have hinner' : execIRStmts
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR
                  ]] ++ tailIR) + extraFuel - 1)
          state
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ] =
          .revert next := by
        simpa [hir] using hinner
      simpa [hir] using
          (execIRStmt_block_of_execIRStmts_revert_nonzeroFuel
            (fuel :=
              sizeOf
                ([YulStmt.block
                    [ YulStmt.let_ tempName condIR
                    , YulStmt.if_ (YulExpr.ident tempName) thenIR
                    , YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR
                    ]] ++ tailIR) + extraFuel)
            (state := state)
            (next := next)
            (body :=
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ])
            (compiled_terminal_ite_body_blockStmtFuel_ne_zero
              extraFuel tempName condIR thenIR elseIR tailIR)
            hinner')
  cases hir : irExec
  · rename_i next
    exact False.elim (hirNoContinue next hir)
  · rename_i value next
    have hblock' :
        execIRStmt
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR
                  ]] ++ tailIR) + extraFuel)
          state
          (YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]) =
          .return value next := by
      simpa [hir] using hblock
    have hfuelEq :
        sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel + 1 =
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel) + 1 := by
        omega
    rw [hfuelEq]
    simpa [hir] using
      (execIRStmts_cons_of_execIRStmt_return_anyFuel
          (fuel :=
            sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel)
          (state := state)
          (next := next)
          (stmt :=
            YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ])
          (rest := tailIR)
          (value := value)
        hblock')
  · rename_i next
    have hblock' :
        execIRStmt
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR
                  ]] ++ tailIR) + extraFuel)
          state
          (YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]) =
          .stop next := by
      simpa [hir] using hblock
    have hfuelEq :
        sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel + 1 =
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel) + 1 := by
        omega
    rw [hfuelEq]
    simpa [hir] using
      (execIRStmts_cons_of_execIRStmt_stop_anyFuel
          (fuel :=
            sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel)
          (state := state)
          (next := next)
          (stmt :=
            YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ])
          (rest := tailIR)
        hblock')
  · rename_i next
    have hblock' :
        execIRStmt
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR
                  ]] ++ tailIR) + extraFuel)
          state
          (YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]) =
          .revert next := by
      simpa [hir] using hblock
    have hfuelEq :
        sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel + 1 =
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel) + 1 := by
        omega
    rw [hfuelEq]
    simpa [hir] using
      (execIRStmts_cons_of_execIRStmt_revert_anyFuel
          (fuel :=
            sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel)
          (state := state)
          (next := next)
          (stmt :=
            YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ])
          (rest := tailIR)
        hblock')

private theorem execIRStmts_compiled_terminal_ite_else_of_irExec
    (extraFuel : Nat)
    (state : IRState)
    (tempName : String)
    (condIR : YulExpr)
    (thenIR elseIR tailIR : List YulStmt)
    (condValue : Nat)
    (irExec : IRExecResult)
    (hcond : evalIRExpr state condIR = some condValue)
    (hcondZero : condValue = 0)
    (helseExec :
      execIRStmts
        (sizeOf elseIR +
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) -
            (sizeOf elseIR + 5) +
            extraFuel))
        (state.setVar tempName condValue) elseIR = irExec)
    (hirNoContinue : ∀ next, irExec ≠ .continue next) :
    execIRStmts
      (sizeOf
          ([YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_
                  (YulExpr.call "iszero" [YulExpr.ident tempName])
                  elseIR
              ]] ++ tailIR) + extraFuel + 1)
      state
      ([YulStmt.block
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_
              (YulExpr.call "iszero" [YulExpr.ident tempName])
              elseIR
          ]] ++ tailIR) = irExec := by
  have hlet :=
    execIRStmt_compiled_terminal_ite_let
      extraFuel state tempName condIR thenIR elseIR tailIR condValue hcond
  have hthenStmt :
      execIRStmt
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 3)
        (state.setVar tempName condValue)
        (YulStmt.if_ (YulExpr.ident tempName) thenIR) =
      .continue (state.setVar tempName condValue) := by
    exact execIRStmt_compiled_terminal_ite_thenIf_false
      extraFuel state tempName condIR thenIR elseIR tailIR condValue hcondZero
  have helseStmt :
      execIRStmt
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 4)
        (state.setVar tempName condValue)
        (YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR) = irExec := by
    rw [execIRStmt_compiled_terminal_ite_else_branch_entry_tailFuel
      extraFuel state tempName condIR thenIR elseIR tailIR condValue hcondZero]
    exact helseExec
  have hafterThen :
      execIRStmts
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 2)
        (state.setVar tempName condValue)
        [ YulStmt.if_ (YulExpr.ident tempName) thenIR
        , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ] = irExec := by
    have hfuelEq :
        sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 2 =
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel - 3) + 1 := by
      have hblock :=
        (compiled_terminal_ite_body_size_ge_branchExecFuel tempName condIR thenIR elseIR tailIR).1
      omega
    rw [hfuelEq]
    rw [execIRStmts_cons_of_execIRStmt_continue_anyFuel
      (fuel :=
        sizeOf
          ([YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_
                  (YulExpr.call "iszero" [YulExpr.ident tempName])
                  elseIR
              ]] ++ tailIR) + extraFuel - 3)
      (state := state.setVar tempName condValue)
      (next := state.setVar tempName condValue)
      (stmt := YulStmt.if_ (YulExpr.ident tempName) thenIR)
      (rest := [YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR])
      hthenStmt]
    have hfuelEq' :
        sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 3 =
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel - 4) + 1 := by
      have hblock :=
        (compiled_terminal_ite_body_size_ge_branchExecFuel tempName condIR thenIR elseIR tailIR).2
      omega
    rw [hfuelEq']
    cases hir : irExec
    · rename_i next
      exact False.elim (hirNoContinue next hir)
    · rename_i value next
      have helseStmt' :
          execIRStmt
            (sizeOf
                ([YulStmt.block
                    [ YulStmt.let_ tempName condIR
                    , YulStmt.if_ (YulExpr.ident tempName) thenIR
                    , YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR
                    ]] ++ tailIR) + extraFuel - 4)
            (state.setVar tempName condValue)
            (YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR) =
            .return value next := by
        simpa [hir] using helseStmt
      simpa [hir] using
          (execIRStmts_cons_of_execIRStmt_return_anyFuel
            (fuel :=
              sizeOf
                ([YulStmt.block
                    [ YulStmt.let_ tempName condIR
                    , YulStmt.if_ (YulExpr.ident tempName) thenIR
                    , YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR
                    ]] ++ tailIR) + extraFuel - 4)
            (state := state.setVar tempName condValue)
            (next := next)
            (stmt := YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR)
            (rest := [])
            (value := value)
            helseStmt')
    · rename_i next
      have helseStmt' :
          execIRStmt
            (sizeOf
                ([YulStmt.block
                    [ YulStmt.let_ tempName condIR
                    , YulStmt.if_ (YulExpr.ident tempName) thenIR
                    , YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR
                    ]] ++ tailIR) + extraFuel - 4)
            (state.setVar tempName condValue)
            (YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR) =
            .stop next := by
        simpa [hir] using helseStmt
      simpa [hir] using
          (execIRStmts_cons_of_execIRStmt_stop_anyFuel
            (fuel :=
              sizeOf
                ([YulStmt.block
                    [ YulStmt.let_ tempName condIR
                    , YulStmt.if_ (YulExpr.ident tempName) thenIR
                    , YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR
                    ]] ++ tailIR) + extraFuel - 4)
            (state := state.setVar tempName condValue)
            (next := next)
            (stmt := YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR)
            (rest := [])
            helseStmt')
    · rename_i next
      have helseStmt' :
          execIRStmt
            (sizeOf
                ([YulStmt.block
                    [ YulStmt.let_ tempName condIR
                    , YulStmt.if_ (YulExpr.ident tempName) thenIR
                    , YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR
                    ]] ++ tailIR) + extraFuel - 4)
            (state.setVar tempName condValue)
            (YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR) =
            .revert next := by
        simpa [hir] using helseStmt
      simpa [hir] using
          (execIRStmts_cons_of_execIRStmt_revert_anyFuel
            (fuel :=
              sizeOf
                ([YulStmt.block
                    [ YulStmt.let_ tempName condIR
                    , YulStmt.if_ (YulExpr.ident tempName) thenIR
                    , YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR
                    ]] ++ tailIR) + extraFuel - 4)
            (state := state.setVar tempName condValue)
            (next := next)
            (stmt := YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR)
            (rest := [])
            helseStmt')
  have hinner :
      execIRStmts
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 1)
        state
        [ YulStmt.let_ tempName condIR
        , YulStmt.if_ (YulExpr.ident tempName) thenIR
        , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ] = irExec := by
    have hfuelEq :
        sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel - 1 =
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel - 2) + 1 := by
      have hblock :=
        (compiled_terminal_ite_body_size_ge_branchExecFuel tempName condIR thenIR elseIR tailIR).1
      omega
    rw [hfuelEq]
    rw [execIRStmts_cons_of_execIRStmt_continue_anyFuel
      (fuel :=
        sizeOf
          ([YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_
                  (YulExpr.call "iszero" [YulExpr.ident tempName])
                  elseIR
              ]] ++ tailIR) + extraFuel - 2)
      (state := state)
      (next := state.setVar tempName condValue)
      (stmt := YulStmt.let_ tempName condIR)
      (rest :=
        [ YulStmt.if_ (YulExpr.ident tempName) thenIR
        , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ])
      hlet]
    exact hafterThen
  have hblock :
      execIRStmt
        (sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel)
        state
        (YulStmt.block
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]) = irExec := by
    cases hir : irExec
    · rename_i next
      exact False.elim (hirNoContinue next hir)
    · rename_i value next
      have hinner' : execIRStmts
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR
                  ]] ++ tailIR) + extraFuel - 1)
          state
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ] =
          .return value next := by
        simpa [hir] using hinner
      simpa [hir] using
          (execIRStmt_block_of_execIRStmts_return_nonzeroFuel
            (fuel :=
              sizeOf
                ([YulStmt.block
                    [ YulStmt.let_ tempName condIR
                    , YulStmt.if_ (YulExpr.ident tempName) thenIR
                    , YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR
                    ]] ++ tailIR) + extraFuel)
            (state := state)
            (next := next)
            (body :=
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ])
            (value := value)
            (compiled_terminal_ite_body_blockStmtFuel_ne_zero
              extraFuel tempName condIR thenIR elseIR tailIR)
            hinner')
    · rename_i next
      have hinner' : execIRStmts
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR
                  ]] ++ tailIR) + extraFuel - 1)
          state
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ] =
          .stop next := by
        simpa [hir] using hinner
      simpa [hir] using
          (execIRStmt_block_of_execIRStmts_stop_nonzeroFuel
            (fuel :=
              sizeOf
                ([YulStmt.block
                    [ YulStmt.let_ tempName condIR
                    , YulStmt.if_ (YulExpr.ident tempName) thenIR
                    , YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR
                    ]] ++ tailIR) + extraFuel)
            (state := state)
            (next := next)
            (body :=
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ])
            (compiled_terminal_ite_body_blockStmtFuel_ne_zero
              extraFuel tempName condIR thenIR elseIR tailIR)
            hinner')
    · rename_i next
      have hinner' : execIRStmts
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR
                  ]] ++ tailIR) + extraFuel - 1)
          state
          [ YulStmt.let_ tempName condIR
          , YulStmt.if_ (YulExpr.ident tempName) thenIR
          , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ] =
          .revert next := by
        simpa [hir] using hinner
      simpa [hir] using
          (execIRStmt_block_of_execIRStmts_revert_nonzeroFuel
            (fuel :=
              sizeOf
                ([YulStmt.block
                    [ YulStmt.let_ tempName condIR
                    , YulStmt.if_ (YulExpr.ident tempName) thenIR
                    , YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR
                    ]] ++ tailIR) + extraFuel)
            (state := state)
            (next := next)
            (body :=
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ])
            (compiled_terminal_ite_body_blockStmtFuel_ne_zero
              extraFuel tempName condIR thenIR elseIR tailIR)
            hinner')
  cases hir : irExec
  · rename_i next
    exact False.elim (hirNoContinue next hir)
  · rename_i value next
    have hblock' :
        execIRStmt
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR
                  ]] ++ tailIR) + extraFuel)
          state
          (YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]) =
          .return value next := by
      simpa [hir] using hblock
    have hfuelEq :
        sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel + 1 =
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel) + 1 := by
        omega
    rw [hfuelEq]
    simpa [hir] using
      (execIRStmts_cons_of_execIRStmt_return_anyFuel
          (fuel :=
            sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel)
          (state := state)
          (next := next)
          (stmt :=
            YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ])
          (rest := tailIR)
          (value := value)
        hblock')
  · rename_i next
    have hblock' :
        execIRStmt
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR
                  ]] ++ tailIR) + extraFuel)
          state
          (YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]) =
          .stop next := by
      simpa [hir] using hblock
    have hfuelEq :
        sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel + 1 =
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel) + 1 := by
        omega
    rw [hfuelEq]
    simpa [hir] using
      (execIRStmts_cons_of_execIRStmt_stop_anyFuel
          (fuel :=
            sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel)
          (state := state)
          (next := next)
          (stmt :=
            YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ])
          (rest := tailIR)
        hblock')
  · rename_i next
    have hblock' :
        execIRStmt
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR
                  ]] ++ tailIR) + extraFuel)
          state
          (YulStmt.block
            [ YulStmt.let_ tempName condIR
            , YulStmt.if_ (YulExpr.ident tempName) thenIR
            , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]) =
          .revert next := by
      simpa [hir] using hblock
    have hfuelEq :
        sizeOf
            ([YulStmt.block
                [ YulStmt.let_ tempName condIR
                , YulStmt.if_ (YulExpr.ident tempName) thenIR
                , YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR
                ]] ++ tailIR) + extraFuel + 1 =
          (sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel) + 1 := by
        omega
    rw [hfuelEq]
    simpa [hir] using
      (execIRStmts_cons_of_execIRStmt_revert_anyFuel
          (fuel :=
            sizeOf
              ([YulStmt.block
                  [ YulStmt.let_ tempName condIR
                  , YulStmt.if_ (YulExpr.ident tempName) thenIR
                  , YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR
                  ]] ++ tailIR) + extraFuel)
          (state := state)
          (next := next)
          (stmt :=
            YulStmt.block
              [ YulStmt.let_ tempName condIR
              , YulStmt.if_ (YulExpr.ident tempName) thenIR
              , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ])
          (rest := tailIR)
        hblock')

theorem execStmtList_terminal_core_not_continue
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {scope : List String}
    {stmts : List Stmt}
    (hterminal : StmtListTerminalCore scope stmts) :
    ∀ next, SourceSemantics.execStmtList fields runtime stmts ≠ .continue next := by
   induction hterminal generalizing runtime with
   | letVar hvalue hinScope hrest ih =>
       rename_i scope name value rest
       let runtime' :=
         { runtime with
           bindings := SourceSemantics.bindValue runtime.bindings name
             (SourceSemantics.evalExpr fields runtime value) }
       simpa [SourceSemantics.execStmtList, SourceSemantics.execStmt, runtime'] using
         ih (runtime := runtime')
   | assignVar hvalue hinScope hrest ih =>
       rename_i scope name value rest
       let runtime' :=
         { runtime with
           bindings := SourceSemantics.bindValue runtime.bindings name
             (SourceSemantics.evalExpr fields runtime value) }
       simpa [SourceSemantics.execStmtList, SourceSemantics.execStmt, runtime'] using
         ih (runtime := runtime')
   | require_ hcond hinScope hrest ih =>
       rename_i scope cond message rest
       by_cases hcondTrue : (SourceSemantics.evalExpr fields runtime cond != 0) = true
       · simpa [SourceSemantics.execStmtList, SourceSemantics.execStmt, hcondTrue] using
           ih (runtime := runtime)
       · have hcondFalse : (SourceSemantics.evalExpr fields runtime cond != 0) = false := by
           cases hbool : (SourceSemantics.evalExpr fields runtime cond != 0) <;> simp_all
         simp [SourceSemantics.execStmtList, SourceSemantics.execStmt, hcondFalse]
   | return_ hvalue hinScope hrest =>
       rename_i scope value rest
       intro next
       simp [SourceSemantics.execStmtList, SourceSemantics.execStmt]
   | stop hrest =>
       rename_i scope rest
       intro next
       simp [SourceSemantics.execStmtList, SourceSemantics.execStmt]
   | ite hcond hinScope hthen helse hrest ihThen ihElse =>
       rename_i scope cond thenBranch elseBranch rest
       by_cases hcondTrue : (SourceSemantics.evalExpr fields runtime cond != 0) = true
       · intro next
         have hthenNoContinue := ihThen (runtime := runtime)
         simp [SourceSemantics.execStmtList, SourceSemantics.execStmt, hcondTrue]
         intro hEq
         cases hthenExec : SourceSemantics.execStmtList fields runtime thenBranch <;> simp [hthenExec] at hEq
         · rename_i next'
           exact hthenNoContinue next' hthenExec
       · intro next
         have helseNoContinue := ihElse (runtime := runtime)
         have hcondFalse : (SourceSemantics.evalExpr fields runtime cond != 0) = false := by
           cases hbool : (SourceSemantics.evalExpr fields runtime cond != 0) <;> simp_all
         simp [SourceSemantics.execStmtList, SourceSemantics.execStmt, hcondFalse]
         intro hEq
         cases helseExec : SourceSemantics.execStmtList fields runtime elseBranch <;> simp [helseExec] at hEq
         · rename_i next'
           exact helseNoContinue next' helseExec

theorem stmtResultMatchesIRExec_ir_not_continue_of_source_not_continue
    {fields : List Field}
    {sourceResult : SourceSemantics.StmtResult}
    {irExec : IRExecResult}
    (hsourceNoContinue : ∀ next, sourceResult ≠ .continue next)
    (hmatch : stmtResultMatchesIRExec fields sourceResult irExec) :
    ∀ next, irExec ≠ .continue next := by
  intro next hcontinue
  cases sourceResult <;> cases irExec <;> simp [stmtResultMatchesIRExec] at hmatch hcontinue
  rename_i runtime state
  exact hsourceNoContinue runtime rfl

theorem stmtResultMatchesIRExec_ir_not_continue_of_terminal_core
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {scope : List String}
    {stmts : List Stmt}
    {irExec : IRExecResult}
    (hterminal : StmtListTerminalCore scope stmts)
    (hmatch :
      stmtResultMatchesIRExec fields
        (SourceSemantics.execStmtList fields runtime stmts)
        irExec) :
    ∀ next, irExec ≠ .continue next := by
  exact stmtResultMatchesIRExec_ir_not_continue_of_source_not_continue
    (fields := fields)
    (sourceResult := SourceSemantics.execStmtList fields runtime stmts)
    (irExec := irExec)
    (execStmtList_terminal_core_not_continue
      (fields := fields)
      (runtime := runtime)
      (scope := scope)
      (stmts := stmts)
      hterminal)
    hmatch

 theorem execStmtList_terminal_core_ite_then_eq
     {fields : List Field}
     {runtime : SourceSemantics.RuntimeState}
     {scope : List String}
     {cond : Expr}
     {thenBranch elseBranch rest : List Stmt}
     (hthen : StmtListTerminalCore scope thenBranch)
     (hcondTrue : (SourceSemantics.evalExpr fields runtime cond != 0) = true) :
     SourceSemantics.execStmtList fields runtime (.ite cond thenBranch elseBranch :: rest) =
       SourceSemantics.execStmtList fields runtime thenBranch := by

   rw [SourceSemantics.execStmtList, SourceSemantics.execStmt, hcondTrue]
   cases hthenExec : SourceSemantics.execStmtList fields runtime thenBranch <;> simp [hthenExec]
   rename_i next
   exact False.elim <|
     execStmtList_terminal_core_not_continue
       (fields := fields)
       (runtime := runtime)
       (scope := scope)
       (stmts := thenBranch)
       hthen next hthenExec

 theorem execStmtList_terminal_core_ite_else_eq
     {fields : List Field}
     {runtime : SourceSemantics.RuntimeState}
     {scope : List String}
     {cond : Expr}
     {thenBranch elseBranch rest : List Stmt}
     (helse : StmtListTerminalCore scope elseBranch)
     (hcondFalse : (SourceSemantics.evalExpr fields runtime cond != 0) = false) :
     SourceSemantics.execStmtList fields runtime (.ite cond thenBranch elseBranch :: rest) =
       SourceSemantics.execStmtList fields runtime elseBranch := by

   rw [SourceSemantics.execStmtList, SourceSemantics.execStmt, hcondFalse]
   cases helseExec : SourceSemantics.execStmtList fields runtime elseBranch <;> simp [helseExec]
   rename_i next
   exact False.elim <|
     execStmtList_terminal_core_not_continue
       (fields := fields)
       (runtime := runtime)
       (scope := scope)
       (stmts := elseBranch)
       helse next helseExec

 theorem stmtResultMatchesIRExec_compiled_terminal_ite_then
     {fields : List Field}
     {runtime : SourceSemantics.RuntimeState}
     {state : IRState}
     {scope : List String}
     {cond : Expr}
     {thenBranch elseBranch rest : List Stmt}
     {extraFuel : Nat}
     {tempName : String}
     {condIR : YulExpr}
     {thenIR elseIR tailIR : List YulStmt}
     {condValue : Nat}
     {irExec : IRExecResult}
     (hthen : StmtListTerminalCore scope thenBranch)
     (hmatch :
       stmtResultMatchesIRExec fields
         (SourceSemantics.execStmtList fields runtime thenBranch)
         irExec)
     (hcondTrue : (SourceSemantics.evalExpr fields runtime cond != 0) = true)
     (hcond : evalIRExpr state condIR = some condValue)
     (hcondNonzero : condValue ≠ 0)
     (hthenExec :
       execIRStmts
         (sizeOf thenIR +
           (sizeOf
               ([YulStmt.block
                   [ YulStmt.let_ tempName condIR
                   , YulStmt.if_ (YulExpr.ident tempName) thenIR
                   , YulStmt.if_
                       (YulExpr.call "iszero" [YulExpr.ident tempName])
                       elseIR
                   ]] ++ tailIR) -
             (sizeOf thenIR + 5) +
             extraFuel) + 1)
         (state.setVar tempName condValue) thenIR = irExec) :
     stmtResultMatchesIRExec fields
       (SourceSemantics.execStmtList fields runtime (.ite cond thenBranch elseBranch :: rest))
       (execIRStmts
         (sizeOf
             ([YulStmt.block
                 [ YulStmt.let_ tempName condIR
                 , YulStmt.if_ (YulExpr.ident tempName) thenIR
                 , YulStmt.if_
                     (YulExpr.call "iszero" [YulExpr.ident tempName])
                     elseIR
                 ]] ++ tailIR) + extraFuel + 1)
         state
         ([YulStmt.block
             [ YulStmt.let_ tempName condIR
             , YulStmt.if_ (YulExpr.ident tempName) thenIR
             , YulStmt.if_
                 (YulExpr.call "iszero" [YulExpr.ident tempName])
                 elseIR
             ]] ++ tailIR)) := by

   have hirNoContinue :
       ∀ next, irExec ≠ .continue next := by
     exact stmtResultMatchesIRExec_ir_not_continue_of_terminal_core
       (fields := fields)
       (runtime := runtime)
       (scope := scope)
       (stmts := thenBranch)
       (irExec := irExec)
       hthen
       hmatch
   have hsourceEq :
       SourceSemantics.execStmtList fields runtime (.ite cond thenBranch elseBranch :: rest) =
         SourceSemantics.execStmtList fields runtime thenBranch :=
     execStmtList_terminal_core_ite_then_eq
       (fields := fields)
       (runtime := runtime)
       (scope := scope)
       (cond := cond)
       (thenBranch := thenBranch)
       (elseBranch := elseBranch)
       (rest := rest)
       hthen
       hcondTrue
   have hirEq :
       execIRStmts
         (sizeOf
             ([YulStmt.block
                 [ YulStmt.let_ tempName condIR
                 , YulStmt.if_ (YulExpr.ident tempName) thenIR
                 , YulStmt.if_
                     (YulExpr.call "iszero" [YulExpr.ident tempName])
                     elseIR
                 ]] ++ tailIR) + extraFuel + 1)
         state
         ([YulStmt.block
             [ YulStmt.let_ tempName condIR
             , YulStmt.if_ (YulExpr.ident tempName) thenIR
             , YulStmt.if_
                 (YulExpr.call "iszero" [YulExpr.ident tempName])
                 elseIR
             ]] ++ tailIR) =
       irExec :=
     execIRStmts_compiled_terminal_ite_then_of_irExec
       extraFuel state tempName condIR thenIR elseIR tailIR condValue irExec
       hcond hcondNonzero hthenExec hirNoContinue
   rw [hsourceEq, hirEq]
   exact hmatch

 theorem stmtResultMatchesIRExec_compiled_terminal_ite_else
     {fields : List Field}
     {runtime : SourceSemantics.RuntimeState}
     {state : IRState}
     {scope : List String}
     {cond : Expr}
     {thenBranch elseBranch rest : List Stmt}
     {extraFuel : Nat}
     {tempName : String}
     {condIR : YulExpr}
     {thenIR elseIR tailIR : List YulStmt}
     {condValue : Nat}
     {irExec : IRExecResult}
     (helse : StmtListTerminalCore scope elseBranch)
     (hmatch :
       stmtResultMatchesIRExec fields
         (SourceSemantics.execStmtList fields runtime elseBranch)
         irExec)
     (hcondFalse : (SourceSemantics.evalExpr fields runtime cond != 0) = false)
     (hcond : evalIRExpr state condIR = some condValue)
     (hcondZero : condValue = 0)
     (helseExec :
       execIRStmts
         (sizeOf elseIR +
           (sizeOf
               ([YulStmt.block
                   [ YulStmt.let_ tempName condIR
                   , YulStmt.if_ (YulExpr.ident tempName) thenIR
                   , YulStmt.if_
                       (YulExpr.call "iszero" [YulExpr.ident tempName])
                       elseIR
                   ]] ++ tailIR) -
             (sizeOf elseIR + 5) +
             extraFuel))
         (state.setVar tempName condValue) elseIR = irExec) :
     stmtResultMatchesIRExec fields
       (SourceSemantics.execStmtList fields runtime (.ite cond thenBranch elseBranch :: rest))
       (execIRStmts
         (sizeOf
             ([YulStmt.block
                 [ YulStmt.let_ tempName condIR
                 , YulStmt.if_ (YulExpr.ident tempName) thenIR
                 , YulStmt.if_
                     (YulExpr.call "iszero" [YulExpr.ident tempName])
                     elseIR
                 ]] ++ tailIR) + extraFuel + 1)
         state
         ([YulStmt.block
             [ YulStmt.let_ tempName condIR
             , YulStmt.if_ (YulExpr.ident tempName) thenIR
             , YulStmt.if_
                 (YulExpr.call "iszero" [YulExpr.ident tempName])
                 elseIR
             ]] ++ tailIR)) := by

   have hirNoContinue :
       ∀ next, irExec ≠ .continue next := by
     exact stmtResultMatchesIRExec_ir_not_continue_of_terminal_core
       (fields := fields)
       (runtime := runtime)
       (scope := scope)
       (stmts := elseBranch)
       (irExec := irExec)
       helse
       hmatch
   have hsourceEq :
       SourceSemantics.execStmtList fields runtime (.ite cond thenBranch elseBranch :: rest) =
         SourceSemantics.execStmtList fields runtime elseBranch :=
     execStmtList_terminal_core_ite_else_eq
       (fields := fields)
       (runtime := runtime)
       (scope := scope)
       (cond := cond)
       (thenBranch := thenBranch)
       (elseBranch := elseBranch)
       (rest := rest)
       helse
       hcondFalse
   have hirEq :
       execIRStmts
         (sizeOf
             ([YulStmt.block
                 [ YulStmt.let_ tempName condIR
                 , YulStmt.if_ (YulExpr.ident tempName) thenIR
                 , YulStmt.if_
                     (YulExpr.call "iszero" [YulExpr.ident tempName])
                     elseIR
                 ]] ++ tailIR) + extraFuel + 1)
         state
         ([YulStmt.block
             [ YulStmt.let_ tempName condIR
             , YulStmt.if_ (YulExpr.ident tempName) thenIR
             , YulStmt.if_
                 (YulExpr.call "iszero" [YulExpr.ident tempName])
                 elseIR
             ]] ++ tailIR) =
       irExec :=
     execIRStmts_compiled_terminal_ite_else_of_irExec
       extraFuel state tempName condIR thenIR elseIR tailIR condValue irExec
       hcond hcondZero helseExec hirNoContinue
   rw [hsourceEq, hirEq]
   exact hmatch

 theorem execIRStmts_compiled_return_core_append_wholeFuel
     {fields : List Field}
     {runtime : SourceSemantics.RuntimeState}
     {state : IRState}
     {value : Expr}
     {tailIR : List YulStmt}
     {extraFuel : Nat}
     (hcore : ExprCompileCore value)
     (hexact : bindingsExactlyMatchIRVars runtime.bindings state)
     (hbounded : bindingsBounded runtime.bindings)
     (hpresent : exprBoundNamesPresent value runtime.bindings)
     (hruntime : runtimeStateMatchesIR fields runtime state) :
     let retVal := SourceSemantics.evalExpr fields runtime value
     let state' := { state with memory := fun o => if o = 0 then retVal else state.memory o }
     ∃ valueIR,
       CompilationModel.compileExpr fields .calldata value = Except.ok valueIR ∧
       execIRStmts
         (sizeOf
             ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
              , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
               tailIR) + extraFuel + 1)
         state
         ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
          , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
           tailIR) =
         .return retVal state' := by

   rcases compileExpr_core_ok (fields := fields) hcore with ⟨valueIR, hvalueIR⟩
   let retVal := SourceSemantics.evalExpr fields runtime value
   let state' := { state with memory := fun o => if o = 0 then retVal else state.memory o }
   have heval := eval_compileExpr_core hcore hexact hbounded hpresent hruntime
   rw [hvalueIR] at heval
   have heval' : evalIRExpr state valueIR = some retVal := by
     simpa [retVal] using heval
   have hmstoreFuelNeZero :
       sizeOf
           ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
            , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
             tailIR) + extraFuel ≠ 0 := by
     have hprefixLen :
         2 ≤
           ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
            , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
             tailIR).length := by
       simp
     have hlen :
         ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
          , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
           tailIR).length ≤
           sizeOf
             ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
              , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
               tailIR) := by
       exact yulStmtList_length_le_sizeOf _
     omega
   have hreturnFuelNeZero :
       sizeOf
           ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
            , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
             tailIR) + extraFuel - 1 ≠ 0 := by
     have hprefixLen :
         2 ≤
           ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
            , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
             tailIR).length := by
       simp
     have hlen :
         ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
          , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
           tailIR).length ≤
           sizeOf
             ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
              , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
               tailIR) := by
       exact yulStmtList_length_le_sizeOf _
     omega
   have hmstore :
       execIRStmt
           (sizeOf
               ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
                , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
                 tailIR) + extraFuel)
           state
           (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])) =
         .continue state' := by
     simpa [state'] using
       execIRStmt_mstore_of_eval_nonzeroFuel
         (fuel :=
           sizeOf
             ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
              , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
               tailIR) + extraFuel)
         (state := state)
         (offset := 0)
         (valueExpr := valueIR)
         (value := retVal)
         hmstoreFuelNeZero
         heval'
   have hreturn :
       execIRStmt
           (sizeOf
               ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
                , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
                 tailIR) + extraFuel - 1)
           state'
           (YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])) =
         .return retVal state' := by
     simpa [state', retVal] using
       execIRStmt_return32_of_memory_nonzeroFuel
         (fuel :=
           sizeOf
             ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
              , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
               tailIR) + extraFuel - 1)
         (state := state')
         (offset := 0)
         hreturnFuelNeZero
   refine ⟨valueIR, hvalueIR, ?_⟩
   exact execIRStmts_two_append_of_continue_then_return_wholeFuel
     (extraFuel := extraFuel)
     (state := state)
     (mid := state')
     (next := state')
     (stmt1 := YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR]))
     (stmt2 := YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]))
     (rest := tailIR)
     (value := retVal)
     hmstore
     hreturn

 theorem execIRStmts_compiled_return_core_append_wholeFuel_of_scope
     {fields : List Field}
     {runtime : SourceSemantics.RuntimeState}
     {state : IRState}
     {scope : List String}
     {value : Expr}
     {tailIR : List YulStmt}
     {extraFuel : Nat}
     (hcore : ExprCompileCore value)
     (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
     (hinScope : exprBoundNamesInScope value scope)
     (hbounded : bindingsBounded runtime.bindings)
     (hpresent : exprBoundNamesPresent value runtime.bindings)
     (hruntime : runtimeStateMatchesIR fields runtime state) :
     let retVal := SourceSemantics.evalExpr fields runtime value
     let state' := { state with memory := fun o => if o = 0 then retVal else state.memory o }
     ∃ valueIR,
       CompilationModel.compileExpr fields .calldata value = Except.ok valueIR ∧
       execIRStmts
         (sizeOf
             ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
              , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
               tailIR) + extraFuel + 1)
         state
         ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
          , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
           tailIR) =
         .return retVal state' := by

   rcases compileExpr_core_ok (fields := fields) hcore with ⟨valueIR, hvalueIR⟩
   let retVal := SourceSemantics.evalExpr fields runtime value
   let state' := { state with memory := fun o => if o = 0 then retVal else state.memory o }
   have heval :=
     eval_compileExpr_core_of_scope hcore hexact hinScope hbounded hpresent hruntime
   rw [hvalueIR] at heval
   have heval' : evalIRExpr state valueIR = some retVal := by
     simpa [retVal] using heval
   have hmstoreFuelNeZero :
       sizeOf
           ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
            , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
             tailIR) + extraFuel ≠ 0 := by
     have hprefixLen :
         2 ≤
           ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
            , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
             tailIR).length := by
       simp
     have hlen :
         ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
          , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
           tailIR).length ≤
           sizeOf
             ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
              , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
               tailIR) := by
       exact yulStmtList_length_le_sizeOf _
     omega
   have hreturnFuelNeZero :
       sizeOf
           ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
            , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
             tailIR) + extraFuel - 1 ≠ 0 := by
     have hprefixLen :
         2 ≤
           ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
            , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
             tailIR).length := by
       simp
     have hlen :
         ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
          , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
           tailIR).length ≤
           sizeOf
             ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
              , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
               tailIR) := by
       exact yulStmtList_length_le_sizeOf _
     omega
   have hmstore :
       execIRStmt
           (sizeOf
               ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
                , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
                 tailIR) + extraFuel)
           state
           (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])) =
         .continue state' := by
     simpa [state'] using
       execIRStmt_mstore_of_eval_nonzeroFuel
         (fuel :=
           sizeOf
             ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
              , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
               tailIR) + extraFuel)
         (state := state)
         (offset := 0)
         (valueExpr := valueIR)
         (value := retVal)
         hmstoreFuelNeZero
         heval'
   have hreturn :
       execIRStmt
           (sizeOf
               ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
                , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
                 tailIR) + extraFuel - 1)
           state'
           (YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])) =
         .return retVal state' := by
     simpa [state', retVal] using
       execIRStmt_return32_of_memory_nonzeroFuel
         (fuel :=
           sizeOf
             ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
              , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
               tailIR) + extraFuel - 1)
         (state := state')
         (offset := 0)
         hreturnFuelNeZero
   refine ⟨valueIR, hvalueIR, ?_⟩
   exact execIRStmts_two_append_of_continue_then_return_wholeFuel
     (extraFuel := extraFuel)
     (state := state)
     (mid := state')
     (next := state')
     (stmt1 := YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR]))
     (stmt2 := YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]))
     (rest := tailIR)
     (value := retVal)
     hmstore
     hreturn

theorem execIRStmts_compiled_stop_core_append_wholeFuel
    {state : IRState}
    {tailIR : List YulStmt}
    {extraFuel : Nat} :
    execIRStmts
      (sizeOf ([YulStmt.expr (YulExpr.call "stop" [])] ++ tailIR) + extraFuel + 1)
      state
      ([YulStmt.expr (YulExpr.call "stop" [])] ++ tailIR) =
      .stop state := by
  have hstopFuelNeZero :
      sizeOf ([YulStmt.expr (YulExpr.call "stop" [])] ++ tailIR) + extraFuel ≠ 0 := by
    have hprefixLen :
        1 ≤ ([YulStmt.expr (YulExpr.call "stop" [])] ++ tailIR).length := by
      simp
    have hlen :
        ([YulStmt.expr (YulExpr.call "stop" [])] ++ tailIR).length ≤
          sizeOf ([YulStmt.expr (YulExpr.call "stop" [])] ++ tailIR) := by
      exact yulStmtList_length_le_sizeOf _
    omega
  have hstop :
      execIRStmt
          (sizeOf ([YulStmt.expr (YulExpr.call "stop" [])] ++ tailIR) + extraFuel)
          state
          (YulStmt.expr (YulExpr.call "stop" [])) =
        .stop state := by
    exact execIRStmt_stop_nonzeroFuel
      (fuel := sizeOf ([YulStmt.expr (YulExpr.call "stop" [])] ++ tailIR) + extraFuel)
      (state := state)
      hstopFuelNeZero
  exact execIRStmts_singleton_append_of_execIRStmt_stop_wholeFuel
    (extraFuel := extraFuel)
    (state := state)
    (next := state)
    (stmt := YulStmt.expr (YulExpr.call "stop" []))
    (rest := tailIR)
    hstop

private theorem sizeOf_singleton_append_extraFuel_ne_zero
    (stmt : YulStmt)
    (tailIR : List YulStmt)
    (extraFuel : Nat) :
    sizeOf ([stmt] ++ tailIR) + extraFuel ≠ 0 := by
  have hprefixLen : 1 ≤ ([stmt] ++ tailIR).length := by
    simp
  have hlen : ([stmt] ++ tailIR).length ≤ sizeOf ([stmt] ++ tailIR) := by
    exact yulStmtList_length_le_sizeOf _
  omega

 theorem execIRStmts_compiled_let_core_append_wholeFuel_of_scope
     {fields : List Field}
     {runtime : SourceSemantics.RuntimeState}
     {state : IRState}
     {scope : List String}
     {name : String}
     {value : Expr}
     {tailIR : List YulStmt}
     {extraFuel : Nat}
     (hcore : ExprCompileCore value)
     (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
     (hinScope : exprBoundNamesInScope value scope)
     (hscope : scopeNamesPresent scope runtime.bindings)
     (hbounded : bindingsBounded runtime.bindings)
     (hruntime : runtimeStateMatchesIR fields runtime state) :
     let valueNat := SourceSemantics.evalExpr fields runtime value
     let runtime' :=
       { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
     let state' := state.setVar name valueNat
     ∃ valueIR,
       CompilationModel.compileExpr fields .calldata value = Except.ok valueIR ∧
       execIRStmts
         (sizeOf ([YulStmt.let_ name valueIR] ++ tailIR) + extraFuel + 1)
         state
         ([YulStmt.let_ name valueIR] ++ tailIR) =
         execIRStmts
           (sizeOf ([YulStmt.let_ name valueIR] ++ tailIR) + extraFuel)
           state'
           tailIR ∧
       runtimeStateMatchesIR fields runtime' state' ∧
       bindingsExactlyMatchIRVarsOnScope (name :: scope) runtime'.bindings state' ∧
       bindingsBounded runtime'.bindings ∧
       scopeNamesPresent (name :: scope) runtime'.bindings := by

   rcases compileExpr_core_ok (fields := fields) hcore with ⟨valueIR, hvalueIR⟩
   have hpresent : exprBoundNamesPresent value runtime.bindings :=
     exprBoundNamesPresent_of_scope hscope hinScope
   let valueNat := SourceSemantics.evalExpr fields runtime value
   let runtime' :=
     { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
   let state' := state.setVar name valueNat
   have heval :=
     eval_compileExpr_core_of_scope hcore hexact hinScope hbounded hpresent hruntime
   rw [hvalueIR] at heval
   have heval' : evalIRExpr state valueIR = some valueNat := by
     simpa [valueNat] using heval
   have hvalueLt :=
     evalExpr_lt_evmModulus_core_of_scope hcore hexact hinScope hbounded hpresent hruntime
   have hstmt :
       execIRStmt
         (sizeOf ([YulStmt.let_ name valueIR] ++ tailIR) + extraFuel)
         state
         (YulStmt.let_ name valueIR) =
       .continue state' := by
     exact execIRStmt_let_of_eval_nonzeroFuel
       (fuel := sizeOf ([YulStmt.let_ name valueIR] ++ tailIR) + extraFuel)
       (state := state)
       (name := name)
       (valueExpr := valueIR)
       (value := valueNat)
       (sizeOf_singleton_append_extraFuel_ne_zero
         (stmt := YulStmt.let_ name valueIR)
         (tailIR := tailIR)
         (extraFuel := extraFuel))
       heval'
   refine ⟨valueIR, hvalueIR, ?_, ?_⟩
   · exact execIRStmts_singleton_append_of_execIRStmt_continue_wholeFuel
       (extraFuel := extraFuel)
       (state := state)
       (next := state')
       (stmt := YulStmt.let_ name valueIR)
       (rest := tailIR)
       hstmt
   · refine ⟨runtimeStateMatchesIR_setVar_bindValue hruntime name valueNat, ?_⟩
     refine ⟨bindingsExactlyMatchIRVarsOnScope_setVar_bindValue hexact, ?_⟩
     exact ⟨bindingsBounded_bindValue hbounded name valueNat hvalueLt,
       scopeNamesPresent_cons_bindValue hscope⟩

 theorem execIRStmts_compiled_let_core_tailExtraFuel_of_scope
     {fields : List Field}
     {runtime : SourceSemantics.RuntimeState}
     {state : IRState}
     {scope : List String}
     {name : String}
     {value : Expr}
     {valueIR : YulExpr}
     {tailIR : List YulStmt}
     {extraFuel : Nat}
     {irExec : IRExecResult}
     (hcore : ExprCompileCore value)
     (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR)
     (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
     (hinScope : exprBoundNamesInScope value scope)
     (hscope : scopeNamesPresent scope runtime.bindings)
     (hbounded : bindingsBounded runtime.bindings)
     (hruntime : runtimeStateMatchesIR fields runtime state)
     (htail :
       let valueNat := SourceSemantics.evalExpr fields runtime value
       execIRStmts
         (sizeOf tailIR +
           (sizeOf ([YulStmt.let_ name valueIR] ++ tailIR) -
             (sizeOf tailIR + 1) +
             extraFuel) + 1)
         (state.setVar name valueNat)
         tailIR = irExec) :
     let valueNat := SourceSemantics.evalExpr fields runtime value
     let runtime' :=
       { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
     let state' := state.setVar name valueNat
     execIRStmts
       (sizeOf ([YulStmt.let_ name valueIR] ++ tailIR) + extraFuel + 1)
       state
       ([YulStmt.let_ name valueIR] ++ tailIR) = irExec ∧
     runtimeStateMatchesIR fields runtime' state' ∧
     bindingsExactlyMatchIRVarsOnScope (name :: scope) runtime'.bindings state' ∧
     bindingsBounded runtime'.bindings ∧
     scopeNamesPresent (name :: scope) runtime'.bindings := by

   rcases execIRStmts_compiled_let_core_append_wholeFuel_of_scope
       (fields := fields)
       (runtime := runtime)
       (state := state)
       (scope := scope)
       (name := name)
       (value := value)
       (tailIR := tailIR)
       (extraFuel := extraFuel)
       hcore hexact hinScope hscope hbounded hruntime with
     ⟨valueIR', hvalueIR', hwhole, hruntime', hexact', hbounded', hscope'⟩
   rw [hvalueIR] at hvalueIR'
   injection hvalueIR' with hEq
   subst hEq
   let valueNat := SourceSemantics.evalExpr fields runtime value
   let runtime' :=
     { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
   let state' := state.setVar name valueNat
   refine ⟨?_, hruntime', hexact', hbounded', hscope'⟩
   exact execIRStmts_singleton_append_of_execIRStmt_continue_tailExtraFuel
       (extraFuel := extraFuel)
       (state := state)
       (next := state')
       (stmt := YulStmt.let_ name valueIR)
       (rest := tailIR)
       (irExec := irExec)
       (by
         have hpresent : exprBoundNamesPresent value runtime.bindings :=
           exprBoundNamesPresent_of_scope hscope hinScope
         have heval :=
           eval_compileExpr_core_of_scope hcore hexact hinScope hbounded hpresent hruntime
         rw [hvalueIR] at heval
         have heval' : evalIRExpr state valueIR = some valueNat := by
           simpa [valueNat] using heval
         exact execIRStmt_let_of_eval_nonzeroFuel
           (fuel := sizeOf ([YulStmt.let_ name valueIR] ++ tailIR) + extraFuel)
           (state := state)
           (name := name)
           (valueExpr := valueIR)
           (value := valueNat)
           (sizeOf_singleton_append_extraFuel_ne_zero
             (stmt := YulStmt.let_ name valueIR)
             (tailIR := tailIR)
             (extraFuel := extraFuel))
           heval')
       htail

 theorem execIRStmts_compiled_assign_core_append_wholeFuel_of_scope
     {fields : List Field}
     {runtime : SourceSemantics.RuntimeState}
     {state : IRState}
     {scope : List String}
     {name : String}
     {value : Expr}
     {tailIR : List YulStmt}
     {extraFuel : Nat}
     (hcore : ExprCompileCore value)
     (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
     (hinScope : exprBoundNamesInScope value scope)
     (hscope : scopeNamesPresent scope runtime.bindings)
     (hbounded : bindingsBounded runtime.bindings)
     (hruntime : runtimeStateMatchesIR fields runtime state) :
     let valueNat := SourceSemantics.evalExpr fields runtime value
     let runtime' :=
       { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
     let state' := state.setVar name valueNat
     ∃ valueIR,
       CompilationModel.compileExpr fields .calldata value = Except.ok valueIR ∧
       execIRStmts
         (sizeOf ([YulStmt.assign name valueIR] ++ tailIR) + extraFuel + 1)
         state
         ([YulStmt.assign name valueIR] ++ tailIR) =
         execIRStmts
           (sizeOf ([YulStmt.assign name valueIR] ++ tailIR) + extraFuel)
           state'
           tailIR ∧
       runtimeStateMatchesIR fields runtime' state' ∧
       bindingsExactlyMatchIRVarsOnScope (name :: scope) runtime'.bindings state' ∧
       bindingsBounded runtime'.bindings ∧
       scopeNamesPresent (name :: scope) runtime'.bindings := by

   rcases compileExpr_core_ok (fields := fields) hcore with ⟨valueIR, hvalueIR⟩
   have hpresent : exprBoundNamesPresent value runtime.bindings :=
     exprBoundNamesPresent_of_scope hscope hinScope
   let valueNat := SourceSemantics.evalExpr fields runtime value
   let runtime' :=
     { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
   let state' := state.setVar name valueNat
   have heval :=
     eval_compileExpr_core_of_scope hcore hexact hinScope hbounded hpresent hruntime
   rw [hvalueIR] at heval
   have heval' : evalIRExpr state valueIR = some valueNat := by
     simpa [valueNat] using heval
   have hvalueLt :=
     evalExpr_lt_evmModulus_core_of_scope hcore hexact hinScope hbounded hpresent hruntime
   have hstmt :
       execIRStmt
         (sizeOf ([YulStmt.assign name valueIR] ++ tailIR) + extraFuel)
         state
         (YulStmt.assign name valueIR) =
       .continue state' := by
     exact execIRStmt_assign_of_eval_nonzeroFuel
       (fuel := sizeOf ([YulStmt.assign name valueIR] ++ tailIR) + extraFuel)
       (state := state)
       (name := name)
       (valueExpr := valueIR)
       (value := valueNat)
       (sizeOf_singleton_append_extraFuel_ne_zero
         (stmt := YulStmt.assign name valueIR)
         (tailIR := tailIR)
         (extraFuel := extraFuel))
       heval'
   refine ⟨valueIR, hvalueIR, ?_, ?_⟩
   · exact execIRStmts_singleton_append_of_execIRStmt_continue_wholeFuel
       (extraFuel := extraFuel)
       (state := state)
       (next := state')
       (stmt := YulStmt.assign name valueIR)
       (rest := tailIR)
       hstmt
   · refine ⟨runtimeStateMatchesIR_setVar_bindValue hruntime name valueNat, ?_⟩
     refine ⟨bindingsExactlyMatchIRVarsOnScope_setVar_bindValue hexact, ?_⟩
     exact ⟨bindingsBounded_bindValue hbounded name valueNat hvalueLt,
       scopeNamesPresent_cons_bindValue hscope⟩

 theorem execIRStmts_compiled_assign_core_tailExtraFuel_of_scope
     {fields : List Field}
     {runtime : SourceSemantics.RuntimeState}
     {state : IRState}
     {scope : List String}
     {name : String}
     {value : Expr}
     {valueIR : YulExpr}
     {tailIR : List YulStmt}
     {extraFuel : Nat}
     {irExec : IRExecResult}
     (hcore : ExprCompileCore value)
     (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR)
     (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
     (hinScope : exprBoundNamesInScope value scope)
     (hscope : scopeNamesPresent scope runtime.bindings)
     (hbounded : bindingsBounded runtime.bindings)
     (hruntime : runtimeStateMatchesIR fields runtime state)
     (htail :
       let valueNat := SourceSemantics.evalExpr fields runtime value
       execIRStmts
         (sizeOf tailIR +
           (sizeOf ([YulStmt.assign name valueIR] ++ tailIR) -
             (sizeOf tailIR + 1) +
             extraFuel) + 1)
         (state.setVar name valueNat)
         tailIR = irExec) :
     let valueNat := SourceSemantics.evalExpr fields runtime value
     let runtime' :=
       { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
     let state' := state.setVar name valueNat
     execIRStmts
       (sizeOf ([YulStmt.assign name valueIR] ++ tailIR) + extraFuel + 1)
       state
       ([YulStmt.assign name valueIR] ++ tailIR) = irExec ∧
     runtimeStateMatchesIR fields runtime' state' ∧
     bindingsExactlyMatchIRVarsOnScope (name :: scope) runtime'.bindings state' ∧
     bindingsBounded runtime'.bindings ∧
     scopeNamesPresent (name :: scope) runtime'.bindings := by

   rcases execIRStmts_compiled_assign_core_append_wholeFuel_of_scope
       (fields := fields)
       (runtime := runtime)
       (state := state)
       (scope := scope)
       (name := name)
       (value := value)
       (tailIR := tailIR)
       (extraFuel := extraFuel)
       hcore hexact hinScope hscope hbounded hruntime with
     ⟨valueIR', hvalueIR', hwhole, hruntime', hexact', hbounded', hscope'⟩
   rw [hvalueIR] at hvalueIR'
   injection hvalueIR' with hEq
   subst hEq
   let valueNat := SourceSemantics.evalExpr fields runtime value
   let runtime' :=
     { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
   let state' := state.setVar name valueNat
   refine ⟨?_, hruntime', hexact', hbounded', hscope'⟩
   exact execIRStmts_singleton_append_of_execIRStmt_continue_tailExtraFuel
       (extraFuel := extraFuel)
       (state := state)
       (next := state')
       (stmt := YulStmt.assign name valueIR)
       (rest := tailIR)
       (irExec := irExec)
       (by
         have hpresent : exprBoundNamesPresent value runtime.bindings :=
           exprBoundNamesPresent_of_scope hscope hinScope
         have heval :=
           eval_compileExpr_core_of_scope hcore hexact hinScope hbounded hpresent hruntime
         rw [hvalueIR] at heval
         have heval' : evalIRExpr state valueIR = some valueNat := by
           simpa [valueNat] using heval
         exact execIRStmt_assign_of_eval_nonzeroFuel
           (fuel := sizeOf ([YulStmt.assign name valueIR] ++ tailIR) + extraFuel)
           (state := state)
           (name := name)
           (valueExpr := valueIR)
           (value := valueNat)
           (sizeOf_singleton_append_extraFuel_ne_zero
             (stmt := YulStmt.assign name valueIR)
             (tailIR := tailIR)
             (extraFuel := extraFuel))
           heval')
       htail

 theorem execIRStmts_compiled_require_core_pass_append_wholeFuel_of_scope
     {fields : List Field}
     {runtime : SourceSemantics.RuntimeState}
     {state : IRState}
     {scope : List String}
     {cond : Expr}
     {message : String}
     {tailIR : List YulStmt}
     {extraFuel : Nat}
     (hcore : ExprCompileCore cond)
     (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
     (hinScope : exprBoundNamesInScope cond scope)
     (hscope : scopeNamesPresent scope runtime.bindings)
     (hbounded : bindingsBounded runtime.bindings)
     (hruntime : runtimeStateMatchesIR fields runtime state)
     (hcondNeZero : SourceSemantics.evalExpr fields runtime cond ≠ 0) :
     ∃ failCond,
       CompilationModel.compileRequireFailCond fields .calldata cond = Except.ok failCond ∧
       execIRStmts
         (sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) + extraFuel + 1)
         state
         ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) =
         execIRStmts
           (sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) + extraFuel)
           state
           tailIR := by

   have hpresent : exprBoundNamesPresent cond runtime.bindings :=
     exprBoundNamesPresent_of_scope hscope hinScope
   rcases eval_compileRequireFailCond_core_of_scope
       (fields := fields)
       (runtime := runtime)
       (state := state)
       (scope := scope)
       (cond := cond)
       hcore hexact hinScope hbounded hpresent hruntime with
     ⟨failCond, hfailCompile, hfailEval⟩
   have hfailEval' : evalIRExpr state failCond = some 0 := by
     have hdecideFalse : decide (SourceSemantics.evalExpr fields runtime cond = 0) = false := by
       simp [hcondNeZero]
     simpa [SourceSemantics.boolWord, hdecideFalse] using hfailEval
   have hstmt :
       execIRStmt
         (sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) + extraFuel)
         state
         (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) =
       .continue state := by
     exact execIRStmt_if_false_of_eval_nonzeroFuel
       (fuel :=
         sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) + extraFuel)
       (state := state)
       (cond := failCond)
       (body := CompilationModel.revertWithMessage message)
       (value := 0)
       (sizeOf_singleton_append_extraFuel_ne_zero
         (stmt := YulStmt.if_ failCond (CompilationModel.revertWithMessage message))
         (tailIR := tailIR)
         (extraFuel := extraFuel))
       (by simpa [SourceSemantics.boolWord, hcondNeZero] using hfailEval)
       rfl
   refine ⟨failCond, hfailCompile, ?_⟩
   exact execIRStmts_singleton_append_of_execIRStmt_continue_wholeFuel
     (extraFuel := extraFuel)
     (state := state)
     (next := state)
     (stmt := YulStmt.if_ failCond (CompilationModel.revertWithMessage message))
     (rest := tailIR)
     hstmt

 theorem execIRStmts_compiled_require_core_pass_tailExtraFuel_of_scope
     {fields : List Field}
     {runtime : SourceSemantics.RuntimeState}
     {state : IRState}
     {scope : List String}
     {cond : Expr}
     {message : String}
     {failCond : YulExpr}
     {tailIR : List YulStmt}
     {extraFuel : Nat}
     {irExec : IRExecResult}
     (hcore : ExprCompileCore cond)
     (hfailCompile : CompilationModel.compileRequireFailCond fields .calldata cond = Except.ok failCond)
     (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
     (hinScope : exprBoundNamesInScope cond scope)
     (hscope : scopeNamesPresent scope runtime.bindings)
     (hbounded : bindingsBounded runtime.bindings)
     (hruntime : runtimeStateMatchesIR fields runtime state)
     (hcondNeZero : SourceSemantics.evalExpr fields runtime cond ≠ 0)
     (htail :
       execIRStmts
         (sizeOf tailIR +
           (sizeOf
               ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) -
             (sizeOf tailIR + 1) +
             extraFuel) + 1)
         state
         tailIR = irExec) :
     execIRStmts
       (sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) + extraFuel + 1)
       state
       ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) = irExec := by

   rcases execIRStmts_compiled_require_core_pass_append_wholeFuel_of_scope
       (fields := fields)
       (runtime := runtime)
       (state := state)
       (scope := scope)
       (cond := cond)
       (message := message)
       (tailIR := tailIR)
       (extraFuel := extraFuel)
       hcore hexact hinScope hscope hbounded hruntime hcondNeZero with
     ⟨failCond', hfailCompile', hwhole⟩
   rw [hfailCompile] at hfailCompile'
   injection hfailCompile' with hEq
   subst hEq
   exact execIRStmts_singleton_append_of_execIRStmt_continue_tailExtraFuel
     (extraFuel := extraFuel)
     (state := state)
     (next := state)
     (stmt := YulStmt.if_ failCond (CompilationModel.revertWithMessage message))
     (rest := tailIR)
     (irExec := irExec)
     (by
       have hpresent : exprBoundNamesPresent cond runtime.bindings :=
         exprBoundNamesPresent_of_scope hscope hinScope
       rcases eval_compileRequireFailCond_core_of_scope
           (fields := fields)
           (runtime := runtime)
           (state := state)
           (scope := scope)
           (cond := cond)
           hcore hexact hinScope hbounded hpresent hruntime with
         ⟨failCond', hfailCompile', hfailEval⟩
       rw [hfailCompile] at hfailCompile'
       injection hfailCompile' with hEq
       subst hEq
       exact execIRStmt_if_false_of_eval_nonzeroFuel
         (fuel :=
           sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) + extraFuel)
         (state := state)
         (cond := failCond)
         (body := CompilationModel.revertWithMessage message)
         (value := 0)
         (sizeOf_singleton_append_extraFuel_ne_zero
           (stmt := YulStmt.if_ failCond (CompilationModel.revertWithMessage message))
           (tailIR := tailIR)
           (extraFuel := extraFuel))
         (by simpa [SourceSemantics.boolWord, hcondNeZero] using hfailEval)
         rfl)
     htail

 theorem execIRStmts_compiled_require_core_fail_append_wholeFuel_of_scope
     {fields : List Field}
     {runtime : SourceSemantics.RuntimeState}
     {state : IRState}
     {scope : List String}
     {cond : Expr}
     {message : String}
     {tailIR : List YulStmt}
     {extraFuel : Nat}
     (hcore : ExprCompileCore cond)
     (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
     (hinScope : exprBoundNamesInScope cond scope)
     (hscope : scopeNamesPresent scope runtime.bindings)
     (hbounded : bindingsBounded runtime.bindings)
     (hruntime : runtimeStateMatchesIR fields runtime state)
     (hcondZero : SourceSemantics.evalExpr fields runtime cond = 0) :
     ∃ failCond revState,
       CompilationModel.compileRequireFailCond fields .calldata cond = Except.ok failCond ∧
       execIRStmts
         (sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) + extraFuel + 1)
         state
         ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) =
         .revert revState := by

   have hpresent : exprBoundNamesPresent cond runtime.bindings :=
     exprBoundNamesPresent_of_scope hscope hinScope
   rcases eval_compileRequireFailCond_core_of_scope
       (fields := fields)
       (runtime := runtime)
       (state := state)
       (scope := scope)
       (cond := cond)
       hcore hexact hinScope hbounded hpresent hruntime with
     ⟨failCond, hfailCompile, hfailEval⟩
   rcases execIRStmts_revertWithMessage_revert
       (fuel := sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) + extraFuel - 1)
       (state := state)
       message with
     ⟨revState, hrev⟩
   have hfailEval' : evalIRExpr state failCond = some 1 := by
     simpa [hcondZero, SourceSemantics.boolWord] using hfailEval
   have hstmt :
       execIRStmt
         (sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) + extraFuel)
         state
         (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) =
       .revert revState := by
     rw [execIRStmt_if_true_of_eval_nonzeroFuel
         (fuel :=
           sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) + extraFuel)
         (state := state)
         (cond := failCond)
         (body := CompilationModel.revertWithMessage message)
         (value := 1)
         (sizeOf_singleton_append_extraFuel_ne_zero
           (stmt := YulStmt.if_ failCond (CompilationModel.revertWithMessage message))
           (tailIR := tailIR)
           (extraFuel := extraFuel))
         hfailEval'
         (by decide : (1 : Nat) ≠ 0)]
     simpa using hrev
   refine ⟨failCond, revState, hfailCompile, ?_⟩
   exact execIRStmts_singleton_append_of_execIRStmt_revert_wholeFuel
     (extraFuel := extraFuel)
     (state := state)
     (next := revState)
     (stmt := YulStmt.if_ failCond (CompilationModel.revertWithMessage message))
     (rest := tailIR)
     hstmt

 theorem stmtResultMatchesIRExec_compiled_let_core_tailExtraFuel_of_scope
     {fields : List Field}
     {runtime : SourceSemantics.RuntimeState}
     {state : IRState}
     {scope : List String}
     {name : String}
     {value : Expr}
     {valueIR : YulExpr}
     {rest : List Stmt}
     {tailIR : List YulStmt}
     {extraFuel : Nat}
     (hcore : ExprCompileCore value)
     (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR)
     (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
     (hinScope : exprBoundNamesInScope value scope)
     (hscope : scopeNamesPresent scope runtime.bindings)
     (hbounded : bindingsBounded runtime.bindings)
     (hruntime : runtimeStateMatchesIR fields runtime state)
     (htail :
       let valueNat := SourceSemantics.evalExpr fields runtime value
       let runtime' :=
         { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
       stmtResultMatchesIRExec
         fields
         (SourceSemantics.execStmtList fields runtime' rest)
         (execIRStmts
           (sizeOf tailIR +
             (sizeOf ([YulStmt.let_ name valueIR] ++ tailIR) -
               (sizeOf tailIR + 1) +
               extraFuel) + 1)
           (state.setVar name valueNat)
           tailIR)) :
     stmtResultMatchesIRExec
       fields
       (SourceSemantics.execStmtList fields runtime (.letVar name value :: rest))
       (execIRStmts
         (sizeOf ([YulStmt.let_ name valueIR] ++ tailIR) + extraFuel + 1)
         state
         ([YulStmt.let_ name valueIR] ++ tailIR)) := by

   let valueNat := SourceSemantics.evalExpr fields runtime value
   let runtime' :=
     { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
   let state' := state.setVar name valueNat
   rcases execIRStmts_compiled_let_core_tailExtraFuel_of_scope
       (fields := fields)
       (runtime := runtime)
       (state := state)
       (scope := scope)
       (name := name)
       (value := value)
       (valueIR := valueIR)
       (tailIR := tailIR)
       (extraFuel := extraFuel)
       (irExec :=
         execIRStmts
           (sizeOf tailIR +
             (sizeOf ([YulStmt.let_ name valueIR] ++ tailIR) -
               (sizeOf tailIR + 1) +
               extraFuel) + 1)
           state'
           tailIR)
       hcore hvalueIR hexact hinScope hscope hbounded hruntime rfl with
     ⟨hwhole, hruntime', hexact', hbounded', hscope'⟩
   have hwhole' :
       execIRStmts
         (1 + (1 + sizeOf name + sizeOf valueIR) + sizeOf tailIR + extraFuel + 1)
         state
         (YulStmt.let_ name valueIR :: tailIR) =
       execIRStmts
         (sizeOf tailIR +
           (sizeOf ([YulStmt.let_ name valueIR] ++ tailIR) -
             (sizeOf tailIR + 1) +
             extraFuel) + 1)
         state'
         tailIR := by
     simpa using hwhole
   rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
   dsimp [runtime', valueNat]
   rw [hwhole']
   exact htail

 theorem stmtResultMatchesIRExec_compiled_assign_core_tailExtraFuel_of_scope
     {fields : List Field}
     {runtime : SourceSemantics.RuntimeState}
     {state : IRState}
     {scope : List String}
     {name : String}
     {value : Expr}
     {valueIR : YulExpr}
     {rest : List Stmt}
     {tailIR : List YulStmt}
     {extraFuel : Nat}
     (hcore : ExprCompileCore value)
     (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR)
     (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
     (hinScope : exprBoundNamesInScope value scope)
     (hscope : scopeNamesPresent scope runtime.bindings)
     (hbounded : bindingsBounded runtime.bindings)
     (hruntime : runtimeStateMatchesIR fields runtime state)
     (htail :
       let valueNat := SourceSemantics.evalExpr fields runtime value
       let runtime' :=
         { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
       stmtResultMatchesIRExec
         fields
         (SourceSemantics.execStmtList fields runtime' rest)
         (execIRStmts
           (sizeOf tailIR +
             (sizeOf ([YulStmt.assign name valueIR] ++ tailIR) -
               (sizeOf tailIR + 1) +
               extraFuel) + 1)
           (state.setVar name valueNat)
           tailIR)) :
     stmtResultMatchesIRExec
       fields
       (SourceSemantics.execStmtList fields runtime (.assignVar name value :: rest))
       (execIRStmts
         (sizeOf ([YulStmt.assign name valueIR] ++ tailIR) + extraFuel + 1)
         state
         ([YulStmt.assign name valueIR] ++ tailIR)) := by

   let valueNat := SourceSemantics.evalExpr fields runtime value
   let runtime' :=
     { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
   let state' := state.setVar name valueNat
   rcases execIRStmts_compiled_assign_core_tailExtraFuel_of_scope
       (fields := fields)
       (runtime := runtime)
       (state := state)
       (scope := scope)
       (name := name)
       (value := value)
       (valueIR := valueIR)
       (tailIR := tailIR)
       (extraFuel := extraFuel)
       (irExec :=
         execIRStmts
           (sizeOf tailIR +
             (sizeOf ([YulStmt.assign name valueIR] ++ tailIR) -
               (sizeOf tailIR + 1) +
               extraFuel) + 1)
           state'
           tailIR)
       hcore hvalueIR hexact hinScope hscope hbounded hruntime rfl with
     ⟨hwhole, hruntime', hexact', hbounded', hscope'⟩
   have hwhole' :
       execIRStmts
         (1 + (1 + sizeOf name + sizeOf valueIR) + sizeOf tailIR + extraFuel + 1)
         state
         (YulStmt.assign name valueIR :: tailIR) =
       execIRStmts
         (sizeOf tailIR +
           (sizeOf ([YulStmt.assign name valueIR] ++ tailIR) -
             (sizeOf tailIR + 1) +
             extraFuel) + 1)
         state'
         tailIR := by
     simpa using hwhole
   rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
   dsimp [runtime', valueNat]
   rw [hwhole']
   exact htail

 theorem stmtResultMatchesIRExec_compiled_require_core_pass_tailExtraFuel_of_scope
     {fields : List Field}
     {runtime : SourceSemantics.RuntimeState}
     {state : IRState}
     {scope : List String}
     {cond : Expr}
     {message : String}
     {failCond : YulExpr}
     {rest : List Stmt}
     {tailIR : List YulStmt}
     {extraFuel : Nat}
     (hcore : ExprCompileCore cond)
     (hfailCompile : CompilationModel.compileRequireFailCond fields .calldata cond = Except.ok failCond)
     (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
     (hinScope : exprBoundNamesInScope cond scope)
     (hscope : scopeNamesPresent scope runtime.bindings)
     (hbounded : bindingsBounded runtime.bindings)
     (hruntime : runtimeStateMatchesIR fields runtime state)
     (hcondNeZero : SourceSemantics.evalExpr fields runtime cond ≠ 0)
     (htail :
       stmtResultMatchesIRExec
         fields
         (SourceSemantics.execStmtList fields runtime rest)
         (execIRStmts
           (sizeOf tailIR +
             (sizeOf
                 ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) -
               (sizeOf tailIR + 1) +
               extraFuel) + 1)
           state
           tailIR)) :
     stmtResultMatchesIRExec
       fields
       (SourceSemantics.execStmtList fields runtime (.require cond message :: rest))
       (execIRStmts
         (sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) +
           extraFuel + 1)
         state
         ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR)) := by

   have hwhole :=
     execIRStmts_compiled_require_core_pass_tailExtraFuel_of_scope
       (fields := fields)
       (runtime := runtime)
       (state := state)
       (scope := scope)
       (cond := cond)
       (message := message)
       (failCond := failCond)
       (tailIR := tailIR)
       (extraFuel := extraFuel)
       (irExec :=
         execIRStmts
           (sizeOf tailIR +
             (sizeOf
                 ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) -
               (sizeOf tailIR + 1) +
               extraFuel) + 1)
           state
           tailIR)
       hcore hfailCompile hexact hinScope hscope hbounded hruntime hcondNeZero rfl
   have hcondTrue : (SourceSemantics.evalExpr fields runtime cond != 0) = true := by
     simp [hcondNeZero]
   rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
   rw [hwhole]
   simpa [hcondTrue] using htail

theorem stmtResultMatchesIRExec_compiled_return_core_append_wholeFuel_of_scope
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope : List String}
    {value : Expr}
    {valueIR : YulExpr}
    {rest : List Stmt}
    {tailIR : List YulStmt}
    {extraFuel : Nat}
    (hcore : ExprCompileCore value)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR)
    (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hinScope : exprBoundNamesInScope value scope)
    (hscope : scopeNamesPresent scope runtime.bindings)
    (hbounded : bindingsBounded runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    stmtResultMatchesIRExec
      fields
      (SourceSemantics.execStmtList fields runtime (.return value :: rest))
      (execIRStmts
        (sizeOf
            ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
             , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
              tailIR) + extraFuel + 1)
        state
        ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
         , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
          tailIR)) := by
   rcases execIRStmts_compiled_return_core_append_wholeFuel_of_scope
       (fields := fields)
       (runtime := runtime)
       (state := state)
       (scope := scope)
       (value := value)
       (tailIR := tailIR)
       (extraFuel := extraFuel)
       hcore hexact hinScope hbounded
       (exprBoundNamesPresent_of_scope hscope hinScope)
       hruntime with
     ⟨valueIR', hvalueIR', hwhole⟩
   rw [hvalueIR] at hvalueIR'
   injection hvalueIR' with hEq
   subst hEq
   let retVal := SourceSemantics.evalExpr fields runtime value
   let state' := { state with memory := fun o => if o = 0 then retVal else state.memory o }
   have hmatch :
       stmtResultMatchesIRExec fields
         (SourceSemantics.StmtResult.return retVal runtime)
         (.return retVal state') := by
     exact ⟨rfl, runtimeStateMatchesIR_setMemory hruntime 0 retVal⟩
   have hwhole' :
       execIRStmts
         (1 + (1 + sizeOf (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])) +
             (1 + (1 + sizeOf (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])) + sizeOf tailIR) +
           extraFuel + 1)
         state
         (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR]) ::
           YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) :: tailIR) =
       .return retVal state' := by
     simpa [retVal, state'] using hwhole
   rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
   dsimp [retVal, state']
   rw [hwhole']
   exact hmatch

theorem stmtResultMatchesIRExec_compiled_stop_core_append_wholeFuel
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {rest : List Stmt}
    {tailIR : List YulStmt}
    {extraFuel : Nat}
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    stmtResultMatchesIRExec
      fields
      (SourceSemantics.execStmtList fields runtime (.stop :: rest))
      (execIRStmts
        (sizeOf ([YulStmt.expr (YulExpr.call "stop" [])] ++ tailIR) + extraFuel + 1)
        state
        ([YulStmt.expr (YulExpr.call "stop" [])] ++ tailIR)) := by
  rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
  rw [execIRStmts_compiled_stop_core_append_wholeFuel
    (state := state)
    (tailIR := tailIR)
    (extraFuel := extraFuel)]
  exact hruntime

theorem scopeNamesIncluded_refl
    {scope : List String} :
    scopeNamesIncluded scope scope := by
  intro name hname
  exact hname

theorem scopeNamesIncluded_append_right
    {scope left right : List String}
    (hincluded : scopeNamesIncluded scope right) :
    scopeNamesIncluded scope (left ++ right) := by
  intro name hname
  exact List.mem_append.mpr <| Or.inr (hincluded name hname)

theorem scopeNamesIncluded_collectStmtNames_tail
    {scope inScopeNames : List String}
    {stmt : Stmt}
    (hincluded : scopeNamesIncluded scope inScopeNames) :
    scopeNamesIncluded scope (collectStmtNames stmt ++ inScopeNames) := by
  exact scopeNamesIncluded_append_right (left := collectStmtNames stmt) hincluded

theorem scopeNamesIncluded_collectStmtNames_letVar
    {scope inScopeNames : List String}
    {name : String}
    {value : Expr}
  (hincluded : scopeNamesIncluded scope inScopeNames) :
    scopeNamesIncluded (name :: scope)
      (collectStmtNames (.letVar name value) ++ inScopeNames) := by
  intro other hmem
  simp at hmem
  rcases hmem with rfl | hmem
  · simp [collectStmtNames]
  · simp [collectStmtNames, hincluded other hmem]

theorem scopeNamesIncluded_collectStmtNames_assignVar
    {scope inScopeNames : List String}
    {name : String}
    {value : Expr}
  (hincluded : scopeNamesIncluded scope inScopeNames) :
    scopeNamesIncluded (name :: scope)
      (collectStmtNames (.assignVar name value) ++ inScopeNames) := by
  intro other hmem
  simp at hmem
  rcases hmem with rfl | hmem
  · simp [collectStmtNames]
  · simp [collectStmtNames, hincluded other hmem]

theorem scopeNamesIncluded_compiled_terminal_ite_usedNames
    {scope inScopeNames : List String}
    {cond : Expr}
    {thenBranch elseBranch : List Stmt}
    (hincluded : scopeNamesIncluded scope inScopeNames) :
    scopeNamesIncluded scope
      (inScopeNames ++ collectExprNames cond ++
        collectStmtListNames thenBranch ++ collectStmtListNames elseBranch) := by
  intro name hname
  simp [hincluded name hname]

theorem pickFreshName_not_mem_scope_of_subset
    {base : String}
    {scope usedNames : List String}
    (hsubset : ∀ name, name ∈ scope → name ∈ usedNames) :
    CompilationModel.pickFreshName base usedNames ∉ scope := by
  intro hmem
  exact CompilationModel.pickFreshName_not_mem_usedNames base usedNames (hsubset _ hmem)

theorem bindingsExactlyMatchIRVarsOnScope_setFreshTemp_irrelevant
    {scope : List String}
    {bindings : List (String × Nat)}
    {state : IRState}
    {base : String}
    {usedNames : List String}
    {value : Nat}
    (hexact : bindingsExactlyMatchIRVarsOnScope scope bindings state)
    (hsubset : ∀ name, name ∈ scope → name ∈ usedNames) :
    bindingsExactlyMatchIRVarsOnScope scope bindings
      (state.setVar (CompilationModel.pickFreshName base usedNames) value) := by
  apply bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant hexact
  exact pickFreshName_not_mem_scope_of_subset hsubset

theorem compiled_terminal_ite_temp_not_mem_scope
    {scope inScopeNames : List String}
    {cond : Expr}
    {thenBranch elseBranch : List Stmt}
    (hincluded : scopeNamesIncluded scope inScopeNames) :
    CompilationModel.pickFreshName "__ite_cond"
      (inScopeNames ++ collectExprNames cond ++
        collectStmtListNames thenBranch ++ collectStmtListNames elseBranch) ∉ scope := by
  apply pickFreshName_not_mem_scope_of_subset
  exact scopeNamesIncluded_compiled_terminal_ite_usedNames
    (cond := cond) (thenBranch := thenBranch) (elseBranch := elseBranch) hincluded

theorem bindingsExactlyMatchIRVarsOnScope_setCompiledTerminalIteTemp_irrelevant
    {scope inScopeNames : List String}
    {bindings : List (String × Nat)}
    {state : IRState}
    {cond : Expr}
    {thenBranch elseBranch : List Stmt}
    {value : Nat}
    (hexact : bindingsExactlyMatchIRVarsOnScope scope bindings state)
    (hincluded : scopeNamesIncluded scope inScopeNames) :
    bindingsExactlyMatchIRVarsOnScope scope bindings
      (state.setVar
        (CompilationModel.pickFreshName "__ite_cond"
          (inScopeNames ++ collectExprNames cond ++
            collectStmtListNames thenBranch ++ collectStmtListNames elseBranch))
        value) := by
  apply bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant hexact
  exact compiled_terminal_ite_temp_not_mem_scope
    (cond := cond) (thenBranch := thenBranch) (elseBranch := elseBranch) hincluded

theorem exec_compileStmtList_terminal_core_sizeOf_extraFuel
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope inScopeNames : List String}
    {stmts : List Stmt}
    (extraFuel : Nat)
    (hterminal : StmtListTerminalCore scope stmts)
    (hincluded : scopeNamesIncluded scope inScopeNames)
    (hscope : scopeNamesPresent scope runtime.bindings)
    (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames stmts = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmtList fields runtime stmts
      let irExec := execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR
      stmtResultMatchesIRExec fields sourceResult irExec := by
    induction hterminal generalizing runtime state inScopeNames extraFuel with
   | letVar hvalue hinScope hrest ih =>
       rename_i scope name value rest
       rcases compileExpr_core_ok (fields := fields) hvalue with ⟨valueIR, hvalueIR⟩
       rcases compileStmtList_terminal_core_ok
           (fields := fields)
           (scope := name :: scope)
           (inScopeNames := collectStmtNames (.letVar name value) ++ inScopeNames)
           (stmts := rest)
           hrest with
         ⟨tailIR, htailCompile⟩
       let valueNat := SourceSemantics.evalExpr fields runtime value
       let runtime' :=
         { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
       let state' := state.setVar name valueNat
       let tailExtraFuel :=
         sizeOf ([YulStmt.let_ name valueIR] ++ tailIR) - (sizeOf tailIR + 1) + extraFuel
       rcases ih
           (runtime := runtime')
           (state := state')
           (inScopeNames := collectStmtNames (.letVar name value) ++ inScopeNames)
           (extraFuel := tailExtraFuel)
           (scopeNamesIncluded_collectStmtNames_letVar (name := name) (value := value) hincluded)
           (scopeNamesPresent_cons_bindValue hscope)
           (bindingsExactlyMatchIRVarsOnScope_setVar_bindValue hexact)
           (bindingsBounded_bindValue hbounded name valueNat
             (evalExpr_lt_evmModulus_core_of_scope
               hvalue
               hexact
               hinScope
               hbounded
               (exprBoundNamesPresent_of_scope hscope hinScope)
               hruntime))
           (runtimeStateMatchesIR_setVar_bindValue hruntime name valueNat) with
         ⟨tailIR', htailCompile', htailSem⟩
       rw [htailCompile] at htailCompile'
       injection htailCompile' with htailEq
       subst htailEq
       refine ⟨[YulStmt.let_ name valueIR] ++ tailIR, ?_, ?_⟩
       · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
         rw [hvalueIR]
         simp [htailCompile]
       · exact stmtResultMatchesIRExec_compiled_let_core_tailExtraFuel_of_scope
           (fields := fields)
           (runtime := runtime)
           (state := state)
           (scope := scope)
           (name := name)
           (value := value)
           (valueIR := valueIR)
           (rest := rest)
           (tailIR := tailIR)
           (extraFuel := extraFuel)
           hvalue
           hvalueIR
           hexact
           hinScope
           hscope
           hbounded
           hruntime
           (by
             simpa [tailExtraFuel] using htailSem)
   | assignVar hvalue hinScope hrest ih =>
       rename_i scope name value rest
       rcases compileExpr_core_ok (fields := fields) hvalue with ⟨valueIR, hvalueIR⟩
       rcases compileStmtList_terminal_core_ok
           (fields := fields)
           (scope := name :: scope)
           (inScopeNames := collectStmtNames (.assignVar name value) ++ inScopeNames)
           (stmts := rest)
           hrest with
         ⟨tailIR, htailCompile⟩
       let valueNat := SourceSemantics.evalExpr fields runtime value
       let runtime' :=
         { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
       let state' := state.setVar name valueNat
       let tailExtraFuel :=
         sizeOf ([YulStmt.assign name valueIR] ++ tailIR) - (sizeOf tailIR + 1) + extraFuel
       rcases ih
           (runtime := runtime')
           (state := state')
           (inScopeNames := collectStmtNames (.assignVar name value) ++ inScopeNames)
           (extraFuel := tailExtraFuel)
           (scopeNamesIncluded_collectStmtNames_assignVar (name := name) (value := value) hincluded)
           (scopeNamesPresent_cons_bindValue hscope)
           (bindingsExactlyMatchIRVarsOnScope_setVar_bindValue hexact)
           (bindingsBounded_bindValue hbounded name valueNat
             (evalExpr_lt_evmModulus_core_of_scope
               hvalue
               hexact
               hinScope
               hbounded
               (exprBoundNamesPresent_of_scope hscope hinScope)
               hruntime))
           (runtimeStateMatchesIR_setVar_bindValue hruntime name valueNat) with
         ⟨tailIR', htailCompile', htailSem⟩
       rw [htailCompile] at htailCompile'
       injection htailCompile' with htailEq
       subst htailEq
       refine ⟨[YulStmt.assign name valueIR] ++ tailIR, ?_, ?_⟩
       · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
         rw [hvalueIR]
         simp [htailCompile]
       · exact stmtResultMatchesIRExec_compiled_assign_core_tailExtraFuel_of_scope
           (fields := fields)
           (runtime := runtime)
           (state := state)
           (scope := scope)
           (name := name)
           (value := value)
           (valueIR := valueIR)
           (rest := rest)
           (tailIR := tailIR)
           (extraFuel := extraFuel)
           hvalue
           hvalueIR
           hexact
           hinScope
           hscope
           hbounded
           hruntime
           (by
             simpa [tailExtraFuel] using htailSem)
   | require_ hcond hinScope hrest ih =>
       rename_i scope cond message rest
       have hpresent : exprBoundNamesPresent cond runtime.bindings :=
         exprBoundNamesPresent_of_scope hscope hinScope
       rcases eval_compileRequireFailCond_core_of_scope
           (fields := fields)
           (runtime := runtime)
           (state := state)
           (scope := scope)
           (cond := cond)
           hcond hexact hinScope hbounded hpresent hruntime with
         ⟨failCond, hfailCompile, hfailEval⟩
       rcases compileStmtList_terminal_core_ok
           (fields := fields)
           (scope := scope)
           (inScopeNames := collectStmtNames (.require cond message) ++ inScopeNames)
           (stmts := rest)
           hrest with
         ⟨tailIR, htailCompile⟩
       refine ⟨[YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR, ?_, ?_⟩
       · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
         rw [hfailCompile]
         simp [htailCompile]
       · by_cases hcondZero : SourceSemantics.evalExpr fields runtime cond = 0
         · rcases execIRStmts_compiled_require_core_fail_append_wholeFuel_of_scope
             (fields := fields)
             (runtime := runtime)
             (state := state)
             (scope := scope)
             (cond := cond)
             (message := message)
             (tailIR := tailIR)
             (extraFuel := extraFuel)
             hcond
             hexact
             hinScope
             hscope
             hbounded
             hruntime
             hcondZero with
             ⟨_, _, _, hwhole⟩
           rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
           simp [hcondZero, hwhole, stmtResultMatchesIRExec]
         · let tailExtraFuel :=
             sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) -
               (sizeOf tailIR + 1) + extraFuel
           rcases ih
               (runtime := runtime)
               (state := state)
               (inScopeNames := collectStmtNames (.require cond message) ++ inScopeNames)
               (extraFuel := tailExtraFuel)
               (scopeNamesIncluded_collectStmtNames_tail (stmt := .require cond message) hincluded)
               hscope
               hexact
               hbounded
               hruntime with
             ⟨tailIR', htailCompile', htailSem⟩
           rw [htailCompile] at htailCompile'
           injection htailCompile' with htailEq
           subst htailEq
           exact stmtResultMatchesIRExec_compiled_require_core_pass_tailExtraFuel_of_scope
             (fields := fields)
             (runtime := runtime)
             (state := state)
             (scope := scope)
             (cond := cond)
             (message := message)
             (failCond := failCond)
             (rest := rest)
             (tailIR := tailIR)
             (extraFuel := extraFuel)
             hcond
             hfailCompile
             hexact
             hinScope
             hscope
             hbounded
             hruntime
             (by
               intro hzero
               exact hcondZero hzero)
             (by
               simpa [tailExtraFuel] using htailSem)
   | return_ hvalue hinScope hrest =>
       rename_i scope value rest
       rcases compileExpr_core_ok (fields := fields) hvalue with ⟨valueIR, hvalueIR⟩
       rcases compileStmtList_core_ok
           (fields := fields)
           (scope := scope)
           (inScopeNames := collectStmtNames (.return value) ++ inScopeNames)
           (stmts := rest)
           hrest with
         ⟨tailIR, htailCompile⟩
       refine ⟨[ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
               , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++ tailIR,
         ?_, ?_⟩
       · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
         rw [hvalueIR]
         simp [htailCompile]
       · exact stmtResultMatchesIRExec_compiled_return_core_append_wholeFuel_of_scope
           (fields := fields)
           (runtime := runtime)
           (state := state)
           (scope := scope)
           (value := value)
           (valueIR := valueIR)
           (rest := rest)
           (tailIR := tailIR)
           (extraFuel := extraFuel)
           hvalue
           hvalueIR
           hexact
           hinScope
           hscope
           hbounded
           hruntime
   | stop hrest =>
       rename_i scope rest
       rcases compileStmtList_core_ok
           (fields := fields)
           (scope := scope)
           (inScopeNames := collectStmtNames (.stop) ++ inScopeNames)
           (stmts := rest)
           hrest with
         ⟨tailIR, htailCompile⟩
       refine ⟨[YulStmt.expr (YulExpr.call "stop" [])] ++ tailIR, ?_, ?_⟩
       · simpa [CompilationModel.compileStmtList, CompilationModel.compileStmt, htailCompile]
       · exact stmtResultMatchesIRExec_compiled_stop_core_append_wholeFuel
           (fields := fields)
           (runtime := runtime)
           (state := state)
           (rest := rest)
           (tailIR := tailIR)
           (extraFuel := extraFuel)
           hruntime
   | ite hcond hinScope hthen helse hrest ihThen ihElse =>
       rename_i scope cond thenBranch elseBranch rest
       rcases compileExpr_core_ok (fields := fields) hcond with ⟨condIR, hcondIR⟩
       rcases compileStmtList_terminal_core_ok
           (fields := fields)
           (scope := scope)
           (inScopeNames := inScopeNames)
           (stmts := thenBranch)
           hthen with
         ⟨thenIR, hthenIR⟩
       rcases compileStmtList_terminal_core_ok
           (fields := fields)
           (scope := scope)
           (inScopeNames := inScopeNames)
           (stmts := elseBranch)
           helse with
         ⟨elseIR, helseIR⟩
       rcases compileStmtList_core_ok
           (fields := fields)
           (scope := scope)
           (inScopeNames := collectStmtNames (.ite cond thenBranch elseBranch) ++ inScopeNames)
           (stmts := rest)
           hrest with
         ⟨tailIR, htailIR⟩
       have helseNonempty : elseBranch.isEmpty = false := by
         cases elseBranch with
         | nil =>
             exfalso
             exact stmtListTerminalCore_ne_nil helse rfl
         | cons =>
             simp
       let tempName :=
         CompilationModel.pickFreshName "__ite_cond"
           (inScopeNames ++ collectExprNames cond ++
             collectStmtListNames thenBranch ++ collectStmtListNames elseBranch)
       let bodyIR :=
         [YulStmt.block
           [ YulStmt.let_ tempName condIR
           , YulStmt.if_ (YulExpr.ident tempName) thenIR
           , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]] ++
           tailIR
       refine ⟨bodyIR, ?_, ?_⟩
       · unfold bodyIR tempName
         rw [CompilationModel.compileStmtList]
         unfold CompilationModel.compileStmt
         rw [hcondIR, hthenIR, helseIR]
         dsimp
         rw [htailIR]
         simp [helseNonempty]
       · have hpresent : exprBoundNamesPresent cond runtime.bindings :=
           exprBoundNamesPresent_of_scope hscope hinScope
         let condValue := SourceSemantics.evalExpr fields runtime cond
         have hcondEval :
             evalIRExpr state condIR = some condValue := by
           have heval :=
             eval_compileExpr_core_of_scope hcond hexact hinScope hbounded hpresent hruntime
           rw [hcondIR] at heval
           simpa [condValue] using heval
         by_cases hcondZero : condValue = 0
         · let tailExtraFuel :=
             sizeOf bodyIR - (sizeOf elseIR + 5) + extraFuel
           rcases ihElse
               (runtime := runtime)
               (state := state.setVar tempName condValue)
               (inScopeNames := inScopeNames)
               (extraFuel := tailExtraFuel)
               hincluded
               hscope
               (bindingsExactlyMatchIRVarsOnScope_setCompiledTerminalIteTemp_irrelevant
                 (scope := scope)
                 (inScopeNames := inScopeNames)
                 (cond := cond)
                 (thenBranch := thenBranch)
                 (elseBranch := elseBranch)
                 (value := condValue)
                 hexact
                 hincluded)
               hbounded
               (runtimeStateMatchesIR_setVar_irrelevant hruntime) with
             ⟨elseIR', helseIR', helseSem⟩
           rw [helseIR] at helseIR'
           injection helseIR' with helseEq
           subst helseEq
           exact stmtResultMatchesIRExec_compiled_terminal_ite_else
             (fields := fields)
             (runtime := runtime)
             (state := state)
             (scope := scope)
             (cond := cond)
             (thenBranch := thenBranch)
             (elseBranch := elseBranch)
             (rest := rest)
             (extraFuel := extraFuel)
             (tempName := tempName)
             (condIR := condIR)
             (thenIR := thenIR)
             (elseIR := elseIR)
             (tailIR := tailIR)
             (condValue := condValue)
             (irExec := execIRStmts (sizeOf elseIR + tailExtraFuel) (state.setVar tempName condValue) elseIR)
             helse
             helseSem
             (by simp [condValue, hcondZero])
             hcondEval
             hcondZero
             (by
               simpa [bodyIR, tailExtraFuel, tempName, condValue] using rfl)
         · let tailExtraFuel :=
             sizeOf bodyIR - (sizeOf thenIR + 5) + extraFuel
           rcases ihThen
               (runtime := runtime)
               (state := state.setVar tempName condValue)
               (inScopeNames := inScopeNames)
               (extraFuel := tailExtraFuel)
               hincluded
               hscope
               (bindingsExactlyMatchIRVarsOnScope_setCompiledTerminalIteTemp_irrelevant
                 (scope := scope)
                 (inScopeNames := inScopeNames)
                 (cond := cond)
                 (thenBranch := thenBranch)
                 (elseBranch := elseBranch)
                 (value := condValue)
                 hexact
                 hincluded)
               hbounded
               (runtimeStateMatchesIR_setVar_irrelevant hruntime) with
             ⟨thenIR', hthenIR', hthenSem⟩
           rw [hthenIR] at hthenIR'
           injection hthenIR' with hthenEq
           subst hthenEq
           exact stmtResultMatchesIRExec_compiled_terminal_ite_then
             (fields := fields)
             (runtime := runtime)
             (state := state)
             (scope := scope)
             (cond := cond)
             (thenBranch := thenBranch)
             (elseBranch := elseBranch)
             (rest := rest)
             (extraFuel := extraFuel)
             (tempName := tempName)
             (condIR := condIR)
             (thenIR := thenIR)
             (elseIR := elseIR)
             (tailIR := tailIR)
             (condValue := condValue)
             (irExec := execIRStmts (sizeOf thenIR + tailExtraFuel + 1)
               (state.setVar tempName condValue) thenIR)
             hthen
             hthenSem
             (by simp [condValue, hcondZero])
             hcondEval
             (by
               intro hzero
               exact hcondZero hzero)
             (by
               simpa [bodyIR, tailExtraFuel, tempName, condValue, Nat.add_assoc, Nat.add_left_comm,
                 Nat.add_comm] using rfl)

def irResultOfExecResult (rollback : IRState) : IRExecResult → IRResult
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
        finalStorage := rollback.storage
        finalMappings := Compiler.Proofs.storageAsMappings rollback.storage
        events := rollback.events }

theorem stmtResultToSourceResult_matches_irExecResult
    (spec : CompilationModel)
    (fields : List Field)
    (initialWorld : Verity.ContractState)
    (rollback : IRState)
    (sourceResult : SourceSemantics.StmtResult)
    (irResult : IRExecResult)
    (hrollbackStorage :
      rollback.storage = SourceSemantics.encodeStorage spec initialWorld)
    (hrollbackEvents :
      rollback.events = SourceSemantics.encodeEvents initialWorld.events)
    (hfields : fields = SourceSemantics.effectiveFields spec)
    (hmatch : stmtResultMatchesIRExec fields sourceResult irResult) :
    sourceResultMatchesIRResult
      (stmtResultToSourceResult spec initialWorld sourceResult)
      (irResultOfExecResult rollback irResult) := by
   subst hfields
   cases sourceResult <;> cases irResult <;> simp [stmtResultMatchesIRExec] at hmatch
   ·
     rcases hmatch with ⟨hstorage, _, _, _, _, _, _, _, hnone, hevents⟩
     refine ⟨rfl, hnone.symm, ?_, hevents.symm⟩
     simpa [sourceResultMatchesIRResult, stmtResultToSourceResult,
       SourceSemantics.successResult, SourceSemantics.encodeStorage] using hstorage.symm
   ·
     rcases hmatch with ⟨hstorage, _, _, _, _, _, _, _, hnone, hevents⟩
     refine ⟨rfl, rfl, ?_, hevents.symm⟩
     simpa [sourceResultMatchesIRResult, stmtResultToSourceResult,
       SourceSemantics.successResult, SourceSemantics.encodeStorage] using hstorage.symm
   ·
     rcases hmatch with ⟨rfl, hstorage, _, _, _, _, _, _, _, hnone, hevents⟩
     refine ⟨rfl, rfl, ?_, hevents.symm⟩
     simpa [sourceResultMatchesIRResult, stmtResultToSourceResult,
       SourceSemantics.successResult, SourceSemantics.encodeStorage] using hstorage.symm
   ·
     refine ⟨rfl, rfl, hrollbackStorage.symm, hrollbackEvents.symm⟩

end FunctionBody

end Compiler.Proofs.IRGeneration
