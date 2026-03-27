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
  simp [evalIRExpr, evalIRCall, evalIRExprs, Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext, hsender]
  rfl

theorem evalIRExpr_contractAddress_of_runtimeStateMatchesIR
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (YulExpr.call "address" []) =
      some (SourceSemantics.evalExpr fields runtime (.contractAddress)) := by
  rcases hmatch with ⟨_, _, _, _, hthisAddress, _, _, _, _, _⟩
  have hthisLt : runtime.world.thisAddress.val < Compiler.Constants.evmModulus := by
    have haddrLt : runtime.world.thisAddress.val < Verity.Core.Address.modulus :=
      Verity.Core.Address.val_lt_modulus runtime.world.thisAddress
    dsimp [Verity.Core.Address.modulus, Verity.Core.ADDRESS_MODULUS, Compiler.Constants.evmModulus] at haddrLt ⊢
    omega
  have hthisMod : runtime.world.thisAddress.val % Compiler.Constants.evmModulus =
      runtime.world.thisAddress.val := Nat.mod_eq_of_lt hthisLt
  simp [evalIRExpr, evalIRCall, evalIRExprs, Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext, hthisAddress, hthisMod]
  rfl

theorem evalIRExpr_msgValue_of_runtimeStateMatchesIR
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (YulExpr.call "callvalue" []) =
      some (SourceSemantics.evalExpr fields runtime (.msgValue)) := by
  rcases hmatch with ⟨_, _, _, hmsgValue, _, _, _, _, _, _⟩
  have hmsgLt : runtime.world.msgValue.val < Compiler.Constants.evmModulus := by
    simpa [Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS] using runtime.world.msgValue.isLt
  have hmsgMod : runtime.world.msgValue.val % Compiler.Constants.evmModulus =
      runtime.world.msgValue.val := Nat.mod_eq_of_lt hmsgLt
  simp [evalIRExpr, evalIRCall, evalIRExprs, Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext, hmsgValue, hmsgMod]
  rfl

theorem evalIRExpr_blockTimestamp_of_runtimeStateMatchesIR
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (YulExpr.call "timestamp" []) =
      some (SourceSemantics.evalExpr fields runtime (.blockTimestamp)) := by
  rcases hmatch with ⟨_, _, _, _, _, hblockTimestamp, _, _, _, _⟩
  have htimeLt : runtime.world.blockTimestamp.val < Compiler.Constants.evmModulus := by
    simpa [Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS] using runtime.world.blockTimestamp.isLt
  have htimeMod : runtime.world.blockTimestamp.val % Compiler.Constants.evmModulus =
      runtime.world.blockTimestamp.val := Nat.mod_eq_of_lt htimeLt
  simp [evalIRExpr, evalIRCall, evalIRExprs, Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext, hblockTimestamp, htimeMod]
  rfl

theorem evalIRExpr_blockNumber_of_runtimeStateMatchesIR
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (YulExpr.call "number" []) =
      some (SourceSemantics.evalExpr fields runtime (.blockNumber)) := by
  rcases hmatch with ⟨_, _, _, _, _, _, hblockNumber, _, _, _⟩
  have hnumberLt : runtime.world.blockNumber.val < Compiler.Constants.evmModulus := by
    simpa [Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS] using runtime.world.blockNumber.isLt
  have hnumberMod : runtime.world.blockNumber.val % Compiler.Constants.evmModulus =
      runtime.world.blockNumber.val := Nat.mod_eq_of_lt hnumberLt
  simp [evalIRExpr, evalIRCall, evalIRExprs, Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext, hblockNumber, hnumberMod]
  rfl

theorem evalIRExpr_chainid_of_runtimeStateMatchesIR
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (YulExpr.call "chainid" []) =
      some (SourceSemantics.evalExpr fields runtime (.chainid)) := by
  rcases hmatch with ⟨_, _, _, _, _, _, _, hchainId, _, _⟩
  have hchainLt : runtime.world.chainId.val < Compiler.Constants.evmModulus := by
    simpa [Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS] using runtime.world.chainId.isLt
  have hchainMod : runtime.world.chainId.val % Compiler.Constants.evmModulus =
      runtime.world.chainId.val := Nat.mod_eq_of_lt hchainLt
  simp [evalIRExpr, evalIRCall, evalIRExprs, Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext, hchainId, hchainMod]
  rfl

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
  change some (value % CompilationModel.uint256Modulus) = some (SourceSemantics.wordNormalize value)
  rw [ParamLoading.wordNormalize_eq_mod]
  simp [CompilationModel.uint256Modulus, Compiler.Constants.evmModulus]

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

private theorem maskedWordNormalize_lt_evmModulus (word mask : Nat) :
    SourceSemantics.wordNormalize word &&& mask < Compiler.Constants.evmModulus := by
  have hle : SourceSemantics.wordNormalize word &&& mask ≤ SourceSemantics.wordNormalize word := Nat.and_le_left
  exact Nat.lt_of_le_of_lt hle (wordNormalize_lt_evmModulus word)

private theorem decodeSupportedParamWord_passthrough_lt_evmModulus
    {ty : ParamType}
    {word value : Nat}
    (hpassthrough : ty = .uint256 ∨ ty = .int256 ∨ ty = .bytes32)
    (hdecode : SourceSemantics.decodeSupportedParamWord ty word = some value) :
    value < Compiler.Constants.evmModulus := by
  rcases hpassthrough with rfl | rfl | rfl
  · have hvalue : value = SourceSemantics.wordNormalize word := by
      simpa [SourceSemantics.decodeSupportedParamWord] using hdecode.symm
    cases hvalue
    exact wordNormalize_lt_evmModulus word
  · have hvalue : value = SourceSemantics.wordNormalize word := by
      simpa [SourceSemantics.decodeSupportedParamWord] using hdecode.symm
    cases hvalue
    exact wordNormalize_lt_evmModulus word
  · have hvalue : value = SourceSemantics.wordNormalize word := by
      simpa [SourceSemantics.decodeSupportedParamWord] using hdecode.symm
    cases hvalue
    exact wordNormalize_lt_evmModulus word

private theorem decodeSupportedParamWord_masked_lt_evmModulus
    {ty : ParamType}
    {word value : Nat}
    (hmasked : ty = .uint8 ∨ ty = .address)
    (hdecode : SourceSemantics.decodeSupportedParamWord ty word = some value) :
    value < Compiler.Constants.evmModulus := by
  rcases hmasked with rfl | rfl
  · have hvalue : value = SourceSemantics.wordNormalize word &&& (SourceSemantics.uint8Modulus - 1) := by
      simpa [SourceSemantics.decodeSupportedParamWord] using hdecode.symm
    cases hvalue
    exact maskedWordNormalize_lt_evmModulus word (SourceSemantics.uint8Modulus - 1)
  · have hvalue : value = SourceSemantics.wordNormalize word &&& Compiler.Constants.addressMask := by
      simpa [SourceSemantics.decodeSupportedParamWord] using hdecode.symm
    cases hvalue
    exact maskedWordNormalize_lt_evmModulus word Compiler.Constants.addressMask

private theorem decodeSupportedParamWord_bool_lt_evmModulus
    {word value : Nat}
    (hdecode : SourceSemantics.decodeSupportedParamWord .bool word = some value) :
    value < Compiler.Constants.evmModulus := by
  by_cases hzero : word % Compiler.Constants.evmModulus = 0
  · simp [SourceSemantics.decodeSupportedParamWord, SourceSemantics.wordNormalize, hzero] at hdecode
    cases hdecode
    simp [Compiler.Constants.evmModulus]
  · by_cases hone : word % Compiler.Constants.evmModulus = 1
    · simp [SourceSemantics.decodeSupportedParamWord, SourceSemantics.wordNormalize, hzero, hone] at hdecode
      cases hdecode
      simp [Compiler.Constants.evmModulus]
    · exfalso
      simp [SourceSemantics.decodeSupportedParamWord, SourceSemantics.wordNormalize, hzero, hone] at hdecode

theorem decodeSupportedParamWord_lt_evmModulus
    {ty : ParamType}
    {word value : Nat}
    (hdecode : SourceSemantics.decodeSupportedParamWord ty word = some value) :
    value < Compiler.Constants.evmModulus := by
  cases ty with
  | uint256 =>
      exact decodeSupportedParamWord_passthrough_lt_evmModulus (hpassthrough := .inl rfl) hdecode
  | int256 =>
      exact decodeSupportedParamWord_passthrough_lt_evmModulus (hpassthrough := .inr (.inl rfl)) hdecode
  | uint8 =>
      exact decodeSupportedParamWord_masked_lt_evmModulus (hmasked := .inl rfl) hdecode
  | address =>
      exact decodeSupportedParamWord_masked_lt_evmModulus (hmasked := .inr rfl) hdecode
  | bool =>
      exact decodeSupportedParamWord_bool_lt_evmModulus hdecode
  | bytes32 =>
      exact decodeSupportedParamWord_passthrough_lt_evmModulus (hpassthrough := .inr (.inr rfl)) hdecode
  | string =>
      simp [SourceSemantics.decodeSupportedParamWord] at hdecode
  | tuple _ =>
      simp [SourceSemantics.decodeSupportedParamWord] at hdecode
  | array _ =>
      simp [SourceSemantics.decodeSupportedParamWord] at hdecode
  | fixedArray _ _ =>
      simp [SourceSemantics.decodeSupportedParamWord] at hdecode
  | bytes =>
      simp [SourceSemantics.decodeSupportedParamWord] at hdecode

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
  have hsource : SourceSemantics.evalExpr fields runtime (.param name) = some value := by
    change some (SourceSemantics.lookupValue runtime.bindings name) = some value
    exact congrArg some (lookupValue_eq_of_lookupBinding?_some hlookup)
  have hidentLift :=
    congrArg (fun x => x.bind fun a => some (some a)) hident
  simpa [hsource] using hidentLift
-- SORRY'D:   rcases hpresent name (by simp [exprBoundNames]) with ⟨value, hlookup⟩
-- SORRY'D:   have hident := evalIRExpr_ident_of_exact_bindings hexact name
-- SORRY'D:   rw [hlookup] at hident
-- SORRY'D:   have hsource : SourceSemantics.evalExpr fields runtime (.param name) = value := by
-- SORRY'D:     change SourceSemantics.lookupValue runtime.bindings name = value
-- SORRY'D:     exact lookupValue_eq_of_lookupBinding?_some hlookup
-- SORRY'D:   rw [hsource]
-- SORRY'D:   exact hident

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
  have hsource : SourceSemantics.evalExpr fields runtime (.localVar name) = some value := by
    change some (SourceSemantics.lookupValue runtime.bindings name) = some value
    exact congrArg some (lookupValue_eq_of_lookupBinding?_some hlookup)
  have hidentLift :=
    congrArg (fun x => x.bind fun a => some (some a)) hident
  simpa [hsource] using hidentLift
-- SORRY'D:   rcases hpresent name (by simp [exprBoundNames]) with ⟨value, hlookup⟩
-- SORRY'D:   have hident := evalIRExpr_ident_of_exact_bindings hexact name
-- SORRY'D:   rw [hlookup] at hident
-- SORRY'D:   have hsource : SourceSemantics.evalExpr fields runtime (.localVar name) = value := by
-- SORRY'D:     change SourceSemantics.lookupValue runtime.bindings name = value
-- SORRY'D:     exact lookupValue_eq_of_lookupBinding?_some hlookup
-- SORRY'D:   rw [hsource]
-- SORRY'D:   exact hident

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
  have hsource : SourceSemantics.evalExpr fields runtime (.param name) = some value := by
    change some (SourceSemantics.lookupValue runtime.bindings name) = some value
    exact congrArg some (lookupValue_eq_of_lookupBinding?_some hlookup)
  have hidentLift :=
    congrArg (fun x => x.bind fun a => some (some a)) hident
  simpa [evalIRExpr, hsource] using hidentLift
-- SORRY'D:   rcases hpresent name (by simp [exprBoundNames]) with ⟨value, hlookup⟩
-- SORRY'D:   have hident := hexact name (by simp [exprBoundNames])
-- SORRY'D:   rw [hlookup] at hident
-- SORRY'D:   have hsource : SourceSemantics.evalExpr fields runtime (.param name) = value := by
-- SORRY'D:     change SourceSemantics.lookupValue runtime.bindings name = value
-- SORRY'D:     exact lookupValue_eq_of_lookupBinding?_some hlookup
-- SORRY'D:   rw [hsource]
-- SORRY'D:   simpa [evalIRExpr] using hident

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
  have hsource : SourceSemantics.evalExpr fields runtime (.localVar name) = some value := by
    change some (SourceSemantics.lookupValue runtime.bindings name) = some value
    exact congrArg some (lookupValue_eq_of_lookupBinding?_some hlookup)
  have hidentLift :=
    congrArg (fun x => x.bind fun a => some (some a)) hident
  simpa [evalIRExpr, hsource] using hidentLift
-- SORRY'D:   rcases hpresent name (by simp [exprBoundNames]) with ⟨value, hlookup⟩
-- SORRY'D:   have hident := hexact name (by simp [exprBoundNames])
-- SORRY'D:   rw [hlookup] at hident
-- SORRY'D:   have hsource : SourceSemantics.evalExpr fields runtime (.localVar name) = value := by
-- SORRY'D:     change SourceSemantics.lookupValue runtime.bindings name = value
-- SORRY'D:     exact lookupValue_eq_of_lookupBinding?_some hlookup
-- SORRY'D:   rw [hsource]
-- SORRY'D:   simpa [evalIRExpr] using hident

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

private theorem boolWord_iszero_lt_eq_ge
    (a b : Nat)
    (ha : a < Compiler.Constants.evmModulus)
    (hb : b < Compiler.Constants.evmModulus) :
    SourceSemantics.boolWord
      (SourceSemantics.boolWord (a % Compiler.Constants.evmModulus < b % Compiler.Constants.evmModulus) = 0) =
      SourceSemantics.boolWord (decide (b ≤ a)) := by
  by_cases hlt : a < b
  · have hnotle : ¬ b ≤ a := Nat.not_le_of_gt hlt
    simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, hlt, hnotle, SourceSemantics.boolWord]
  · have hle : b ≤ a := Nat.le_of_not_gt hlt
    simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, hlt, hle, SourceSemantics.boolWord]

private theorem boolWord_iszero_gt_eq_le
    (a b : Nat)
    (ha : a < Compiler.Constants.evmModulus)
    (hb : b < Compiler.Constants.evmModulus) :
    SourceSemantics.boolWord
      (SourceSemantics.boolWord (b % Compiler.Constants.evmModulus < a % Compiler.Constants.evmModulus) = 0) =
      SourceSemantics.boolWord (decide (a ≤ b)) := by
  by_cases hgt : b < a
  · have hnotle : ¬ a ≤ b := Nat.not_le_of_gt hgt
    simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, hgt, hnotle, SourceSemantics.boolWord]
  · have hle : a ≤ b := Nat.le_of_not_gt hgt
    simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, hgt, hle, SourceSemantics.boolWord]

private theorem eval_compileExpr_ge_raw
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
      (CompilationModel.compileExpr fields .calldata (.ge lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.boolWord
          (SourceSemantics.boolWord
            (((SourceSemantics.evalExpr fields runtime lhs).getD 0) % Compiler.Constants.evmModulus <
              ((SourceSemantics.evalExpr fields runtime rhs).getD 0) % Compiler.Constants.evmModulus) = 0)) := by
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' : evalIRExpr state lhsIR = some lhsVal := by
        cases hEval : evalIRExpr state lhsIR with
        | none =>
            simp [hEval, hlhsSrc] at hlhsEval
        | some val =>
            simp [hEval, hlhsSrc] at hlhsEval
            simpa [hlhsEval] using hEval
      have hrhsEval' : evalIRExpr state rhsIR = some rhsVal := by
        cases hEval : evalIRExpr state rhsIR with
        | none =>
            simp [hEval, hrhsSrc] at hrhsEval
        | some val =>
            simp [hEval, hrhsSrc] at hrhsEval
            simpa [hrhsEval] using hEval
      have hcompile :
          (CompilationModel.compileExpr fields .calldata (.ge lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
            YulExpr.call "iszero" [YulExpr.call "lt" [lhsIR, rhsIR]] := by
        rw [CompilationModel.compileExpr, hlhsCompile, hrhsCompile]
        rfl
      rw [hcompile]
      simpa [hlhsSrc, hrhsSrc] using
        (evalIRExpr_iszero_of_lt
          (heval := evalIRExpr_lt_of_eval hlhsEval' hrhsEval')
          (hvalueLt := boolWord_lt_evmModulus _))

private theorem eval_compileExpr_le_raw
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
      (CompilationModel.compileExpr fields .calldata (.le lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.boolWord
          (SourceSemantics.boolWord
            (((SourceSemantics.evalExpr fields runtime rhs).getD 0) % Compiler.Constants.evmModulus <
              ((SourceSemantics.evalExpr fields runtime lhs).getD 0) % Compiler.Constants.evmModulus) = 0)) := by
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' : evalIRExpr state lhsIR = some lhsVal := by
        cases hEval : evalIRExpr state lhsIR with
        | none =>
            simp [hEval, hlhsSrc] at hlhsEval
        | some val =>
            simp [hEval, hlhsSrc] at hlhsEval
            simpa [hlhsEval] using hEval
      have hrhsEval' : evalIRExpr state rhsIR = some rhsVal := by
        cases hEval : evalIRExpr state rhsIR with
        | none =>
            simp [hEval, hrhsSrc] at hrhsEval
        | some val =>
            simp [hEval, hrhsSrc] at hrhsEval
            simpa [hrhsEval] using hEval
      have hcompile :
          (CompilationModel.compileExpr fields .calldata (.le lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
            YulExpr.call "iszero" [YulExpr.call "gt" [lhsIR, rhsIR]] := by
        rw [CompilationModel.compileExpr, hlhsCompile, hrhsCompile]
        rfl
      rw [hcompile]
      simpa [hlhsSrc, hrhsSrc] using
        (evalIRExpr_iszero_of_lt
          (heval := evalIRExpr_gt_of_eval hlhsEval' hrhsEval')
          (hvalueLt := boolWord_lt_evmModulus _))

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

theorem compileExpr_bitAnd_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.bitAnd lhs rhs) =
      Except.ok (YulExpr.call "and" [lhsIR, rhsIR]) := by
  rw [CompilationModel.compileExpr, hlhs, hrhs]
  rfl

theorem compileExpr_bitOr_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.bitOr lhs rhs) =
      Except.ok (YulExpr.call "or" [lhsIR, rhsIR]) := by
  rw [CompilationModel.compileExpr, hlhs, hrhs]
  rfl

theorem compileExpr_bitXor_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.bitXor lhs rhs) =
      Except.ok (YulExpr.call "xor" [lhsIR, rhsIR]) := by
  rw [CompilationModel.compileExpr, hlhs, hrhs]
  rfl

theorem compileExpr_bitNot_ok
    {fields : List Field}
    {expr : Expr}
    {exprIR : YulExpr}
    (hexpr : CompilationModel.compileExpr fields .calldata expr = Except.ok exprIR) :
    CompilationModel.compileExpr fields .calldata (.bitNot expr) =
      Except.ok (YulExpr.call "not" [exprIR]) := by
  rw [CompilationModel.compileExpr, hexpr]
  rfl

theorem compileExpr_min_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.min lhs rhs) =
      Except.ok (YulExpr.call "sub" [lhsIR,
        YulExpr.call "mul" [
          YulExpr.call "sub" [lhsIR, rhsIR],
          YulExpr.call "gt" [lhsIR, rhsIR]
        ]
      ]) := by
  rw [CompilationModel.compileExpr, hlhs, hrhs]
  rfl

theorem compileExpr_max_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.max lhs rhs) =
      Except.ok (YulExpr.call "add" [lhsIR,
        YulExpr.call "mul" [
          YulExpr.call "sub" [rhsIR, lhsIR],
          YulExpr.call "gt" [rhsIR, lhsIR]
        ]
      ]) := by
  rw [CompilationModel.compileExpr, hlhs, hrhs]
  rfl

theorem compileExpr_wMulDown_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.wMulDown lhs rhs) =
      Except.ok (YulExpr.call "div" [
        YulExpr.call "mul" [lhsIR, rhsIR],
        YulExpr.lit 1000000000000000000
      ]) := by
  rw [CompilationModel.compileExpr, hlhs, hrhs]
  rfl

theorem compileExpr_wDivUp_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.wDivUp lhs rhs) =
      Except.ok (YulExpr.call "div" [
        YulExpr.call "add" [
          YulExpr.call "mul" [lhsIR, YulExpr.lit 1000000000000000000],
          YulExpr.call "sub" [rhsIR, YulExpr.lit 1]
        ],
        rhsIR
      ]) := by
  rw [CompilationModel.compileExpr, hlhs, hrhs]
  rfl

theorem compileExpr_ceilDiv_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.ceilDiv lhs rhs) =
      Except.ok (YulExpr.call "mul" [
        YulExpr.call "iszero" [YulExpr.call "iszero" [lhsIR]],
        YulExpr.call "add" [
          YulExpr.call "div" [YulExpr.call "sub" [lhsIR, YulExpr.lit 1], rhsIR],
          YulExpr.lit 1
        ]
      ]) := by
  rw [CompilationModel.compileExpr, hlhs, hrhs]
  rfl

theorem compileExpr_ite_ok
    {fields : List Field}
    {cond thenVal elseVal : Expr}
    {condIR thenIR elseIR : YulExpr}
    (hcond : CompilationModel.compileExpr fields .calldata cond = Except.ok condIR)
    (hthen : CompilationModel.compileExpr fields .calldata thenVal = Except.ok thenIR)
    (helse : CompilationModel.compileExpr fields .calldata elseVal = Except.ok elseIR) :
    CompilationModel.compileExpr fields .calldata (.ite cond thenVal elseVal) =
      Except.ok (YulExpr.call "add" [
        YulExpr.call "mul" [
          YulExpr.call "iszero" [YulExpr.call "iszero" [condIR]],
          thenIR
        ],
        YulExpr.call "mul" [
          YulExpr.call "iszero" [condIR],
          elseIR
        ]
      ]) := by
  rw [CompilationModel.compileExpr, hcond, hthen, helse]
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

private theorem evalIRExpr_of_sourceEval_some
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {expr : Expr}
    {exprIR : YulExpr}
    {value : Nat}
    (hEval : evalIRExpr state exprIR = some (SourceSemantics.evalExpr fields runtime expr))
    (hSource : SourceSemantics.evalExpr fields runtime expr = some value) :
    evalIRExpr state exprIR = some value := by
  cases hIR : evalIRExpr state exprIR with
  | none =>
      simp [hIR, hSource] at hEval
  | some actual =>
      simp [hIR, hSource] at hEval
      simpa [hEval] using hIR

private theorem evalExpr_eq_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {lhs rhs : Expr}
    {lhsVal rhsVal : Nat}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs = some lhsVal)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs = some rhsVal) :
    SourceSemantics.evalExpr fields runtime (.eq lhs rhs) =
      some (SourceSemantics.boolWord (decide (lhsVal = rhsVal))) := by
  calc
    SourceSemantics.evalExpr fields runtime (.eq lhs rhs)
        = (do
            let lhs ← SourceSemantics.evalExpr fields runtime lhs
            let rhs ← SourceSemantics.evalExpr fields runtime rhs
            pure (SourceSemantics.boolWord (decide (lhs = rhs)))) := by
              rfl
    _ = some (SourceSemantics.boolWord (decide (lhsVal = rhsVal))) := by
          simp [hlhs, hrhs]

private theorem evalExpr_lt_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {lhs rhs : Expr}
    {lhsVal rhsVal : Nat}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs = some lhsVal)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs = some rhsVal) :
    SourceSemantics.evalExpr fields runtime (.lt lhs rhs) =
      some (SourceSemantics.boolWord (decide (lhsVal < rhsVal))) := by
  calc
    SourceSemantics.evalExpr fields runtime (.lt lhs rhs)
        = (do
            let lhs ← SourceSemantics.evalExpr fields runtime lhs
            let rhs ← SourceSemantics.evalExpr fields runtime rhs
            pure (SourceSemantics.boolWord (decide (lhs < rhs)))) := by
              rfl
    _ = some (SourceSemantics.boolWord (decide (lhsVal < rhsVal))) := by
          simp [hlhs, hrhs]

private theorem evalExpr_gt_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {lhs rhs : Expr}
    {lhsVal rhsVal : Nat}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs = some lhsVal)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs = some rhsVal) :
    SourceSemantics.evalExpr fields runtime (.gt lhs rhs) =
      some (SourceSemantics.boolWord (decide (rhsVal < lhsVal))) := by
  calc
    SourceSemantics.evalExpr fields runtime (.gt lhs rhs)
        = (do
            let lhs ← SourceSemantics.evalExpr fields runtime lhs
            let rhs ← SourceSemantics.evalExpr fields runtime rhs
            pure (SourceSemantics.boolWord (decide (rhs < lhs)))) := by
              rfl
    _ = some (SourceSemantics.boolWord (decide (rhsVal < lhsVal))) := by
          simp [hlhs, hrhs]

private theorem evalExpr_add_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {lhs rhs : Expr}
    {lhsVal rhsVal : Nat}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs = some lhsVal)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs = some rhsVal) :
    SourceSemantics.evalExpr fields runtime (.add lhs rhs) =
      some ((((lhsVal : Verity.Core.Uint256) + (rhsVal : Verity.Core.Uint256)) :
        Verity.Core.Uint256).val) := by
  calc
    SourceSemantics.evalExpr fields runtime (.add lhs rhs)
        = (do
            let lhs ← do
              let a ← SourceSemantics.evalExpr fields runtime lhs
              pure (Verity.Core.Uint256.ofNat a)
            let rhs ← do
              let a ← SourceSemantics.evalExpr fields runtime rhs
              pure (Verity.Core.Uint256.ofNat a)
            pure (lhs + rhs).val) := by
              rfl
    _ = some ((((lhsVal : Verity.Core.Uint256) + (rhsVal : Verity.Core.Uint256)) :
          Verity.Core.Uint256).val) := by
          simp [hlhs, hrhs]

private theorem evalExpr_mul_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {lhs rhs : Expr}
    {lhsVal rhsVal : Nat}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs = some lhsVal)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs = some rhsVal) :
    SourceSemantics.evalExpr fields runtime (.mul lhs rhs) =
      some ((((lhsVal : Verity.Core.Uint256) * (rhsVal : Verity.Core.Uint256)) :
        Verity.Core.Uint256).val) := by
  calc
    SourceSemantics.evalExpr fields runtime (.mul lhs rhs)
        = (do
            let lhs ← do
              let a ← SourceSemantics.evalExpr fields runtime lhs
              pure (Verity.Core.Uint256.ofNat a)
            let rhs ← do
              let a ← SourceSemantics.evalExpr fields runtime rhs
              pure (Verity.Core.Uint256.ofNat a)
            pure (lhs * rhs).val) := by
              rfl
    _ = some ((((lhsVal : Verity.Core.Uint256) * (rhsVal : Verity.Core.Uint256)) :
          Verity.Core.Uint256).val) := by
          simp [hlhs, hrhs]

private theorem evalExpr_div_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {lhs rhs : Expr}
    {lhsVal rhsVal : Nat}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs = some lhsVal)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs = some rhsVal) :
    SourceSemantics.evalExpr fields runtime (.div lhs rhs) =
      some ((((lhsVal : Verity.Core.Uint256) / (rhsVal : Verity.Core.Uint256)) :
        Verity.Core.Uint256).val) := by
  calc
    SourceSemantics.evalExpr fields runtime (.div lhs rhs)
        = (do
            let lhs ← do
              let a ← SourceSemantics.evalExpr fields runtime lhs
              pure (Verity.Core.Uint256.ofNat a)
            let rhs ← do
              let a ← SourceSemantics.evalExpr fields runtime rhs
              pure (Verity.Core.Uint256.ofNat a)
            pure (lhs / rhs).val) := by
              rfl
    _ = some ((((lhsVal : Verity.Core.Uint256) / (rhsVal : Verity.Core.Uint256)) :
          Verity.Core.Uint256).val) := by
          simp [hlhs, hrhs]

private theorem evalExpr_sub_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {lhs rhs : Expr}
    {lhsVal rhsVal : Nat}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs = some lhsVal)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs = some rhsVal) :
    SourceSemantics.evalExpr fields runtime (.sub lhs rhs) =
      some ((((lhsVal : Verity.Core.Uint256) - (rhsVal : Verity.Core.Uint256)) :
        Verity.Core.Uint256).val) := by
  calc
    SourceSemantics.evalExpr fields runtime (.sub lhs rhs)
        = (do
            let lhs ← do
              let a ← SourceSemantics.evalExpr fields runtime lhs
              pure (Verity.Core.Uint256.ofNat a)
            let rhs ← do
              let a ← SourceSemantics.evalExpr fields runtime rhs
              pure (Verity.Core.Uint256.ofNat a)
            pure (lhs - rhs).val) := by
              rfl
    _ = some ((((lhsVal : Verity.Core.Uint256) - (rhsVal : Verity.Core.Uint256)) :
          Verity.Core.Uint256).val) := by
          simp [hlhs, hrhs]

private theorem evalExpr_mod_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {lhs rhs : Expr}
    {lhsVal rhsVal : Nat}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs = some lhsVal)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs = some rhsVal) :
    SourceSemantics.evalExpr fields runtime (.mod lhs rhs) =
      some ((((lhsVal : Verity.Core.Uint256) % (rhsVal : Verity.Core.Uint256)) :
        Verity.Core.Uint256).val) := by
  calc
    SourceSemantics.evalExpr fields runtime (.mod lhs rhs)
        = (do
            let lhs ← do
              let a ← SourceSemantics.evalExpr fields runtime lhs
              pure (Verity.Core.Uint256.ofNat a)
            let rhs ← do
              let a ← SourceSemantics.evalExpr fields runtime rhs
              pure (Verity.Core.Uint256.ofNat a)
            pure (lhs % rhs).val) := by
              rfl
    _ = some ((((lhsVal : Verity.Core.Uint256) % (rhsVal : Verity.Core.Uint256)) :
          Verity.Core.Uint256).val) := by
          simp [hlhs, hrhs]

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
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' := evalIRExpr_of_sourceEval_some hlhsEval hlhsSrc
      have hrhsEval' := evalIRExpr_of_sourceEval_some hrhsEval hrhsSrc
      have hlhsLt' : lhsVal < Compiler.Constants.evmModulus := by
        simpa [hlhsSrc] using hlhsLt
      have hrhsLt' : rhsVal < Compiler.Constants.evmModulus := by
        simpa [hrhsSrc] using hrhsLt
      have heval :
          evalIRExpr state
            (CompilationModel.compileExpr fields .calldata (.eq lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
              some (SourceSemantics.boolWord
                (lhsVal % Compiler.Constants.evmModulus =
                  rhsVal % Compiler.Constants.evmModulus)) := by
        simpa [hcompile] using evalIRExpr_eq_of_eval hlhsEval' hrhsEval'
      have hsrc := evalExpr_eq_of_values hlhsSrc hrhsSrc
      rw [heval, hsrc]
      simp [Nat.mod_eq_of_lt hlhsLt', Nat.mod_eq_of_lt hrhsLt']
-- SORRY'D:   have hcompile := compileExpr_eq_ok hlhsCompile hrhsCompile
-- SORRY'D:   have heval :
-- SORRY'D:       evalIRExpr state
-- SORRY'D:         (CompilationModel.compileExpr fields .calldata (.eq lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
-- SORRY'D:           some (SourceSemantics.boolWord
-- SORRY'D:             (SourceSemantics.evalExpr fields runtime lhs % Compiler.Constants.evmModulus =
-- SORRY'D:               SourceSemantics.evalExpr fields runtime rhs % Compiler.Constants.evmModulus)) := by
-- SORRY'D:     simpa [hcompile] using evalIRExpr_eq_of_eval hlhsEval hrhsEval
-- SORRY'D:   rw [heval]
-- SORRY'D:   rw [show SourceSemantics.evalExpr fields runtime (.eq lhs rhs) =
-- SORRY'D:       SourceSemantics.boolWord (decide (SourceSemantics.evalExpr fields runtime lhs =
-- SORRY'D:         SourceSemantics.evalExpr fields runtime rhs)) by rfl]
-- SORRY'D:   simp [Nat.mod_eq_of_lt hlhsLt, Nat.mod_eq_of_lt hrhsLt]

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
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' := evalIRExpr_of_sourceEval_some hlhsEval hlhsSrc
      have hrhsEval' := evalIRExpr_of_sourceEval_some hrhsEval hrhsSrc
      have hlhsLt' : lhsVal < Compiler.Constants.evmModulus := by
        simpa [hlhsSrc] using hlhsLt
      have hrhsLt' : rhsVal < Compiler.Constants.evmModulus := by
        simpa [hrhsSrc] using hrhsLt
      have heval :
          evalIRExpr state
            (CompilationModel.compileExpr fields .calldata (.lt lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
              some (SourceSemantics.boolWord
                (lhsVal % Compiler.Constants.evmModulus < rhsVal % Compiler.Constants.evmModulus)) := by
        simpa [hcompile] using evalIRExpr_lt_of_eval hlhsEval' hrhsEval'
      have hsrc := evalExpr_lt_of_values hlhsSrc hrhsSrc
      rw [heval, hsrc]
      simp [Nat.mod_eq_of_lt hlhsLt', Nat.mod_eq_of_lt hrhsLt']
-- SORRY'D:   have hcompile := compileExpr_lt_ok hlhsCompile hrhsCompile
-- SORRY'D:   have heval :
-- SORRY'D:       evalIRExpr state
-- SORRY'D:         (CompilationModel.compileExpr fields .calldata (.lt lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
-- SORRY'D:           some (SourceSemantics.boolWord
-- SORRY'D:             (SourceSemantics.evalExpr fields runtime lhs % Compiler.Constants.evmModulus <
-- SORRY'D:               SourceSemantics.evalExpr fields runtime rhs % Compiler.Constants.evmModulus)) := by
-- SORRY'D:     simpa [hcompile] using evalIRExpr_lt_of_eval hlhsEval hrhsEval
-- SORRY'D:   rw [heval]
-- SORRY'D:   rw [show SourceSemantics.evalExpr fields runtime (.lt lhs rhs) =
-- SORRY'D:       SourceSemantics.boolWord (decide (SourceSemantics.evalExpr fields runtime lhs <
-- SORRY'D:         SourceSemantics.evalExpr fields runtime rhs)) by rfl]
-- SORRY'D:   simp [Nat.mod_eq_of_lt hlhsLt, Nat.mod_eq_of_lt hrhsLt]

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
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' := evalIRExpr_of_sourceEval_some hlhsEval hlhsSrc
      have hrhsEval' := evalIRExpr_of_sourceEval_some hrhsEval hrhsSrc
      have hlhsLt' : lhsVal < Compiler.Constants.evmModulus := by
        simpa [hlhsSrc] using hlhsLt
      have hrhsLt' : rhsVal < Compiler.Constants.evmModulus := by
        simpa [hrhsSrc] using hrhsLt
      have heval :
          evalIRExpr state
            (CompilationModel.compileExpr fields .calldata (.gt lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
              some (SourceSemantics.boolWord
                (rhsVal % Compiler.Constants.evmModulus <
                  lhsVal % Compiler.Constants.evmModulus)) := by
        simpa [hcompile] using evalIRExpr_gt_of_eval hlhsEval' hrhsEval'
      have hsrc := evalExpr_gt_of_values hlhsSrc hrhsSrc
      rw [heval, hsrc]
      simp [Nat.mod_eq_of_lt hlhsLt', Nat.mod_eq_of_lt hrhsLt']
-- SORRY'D:   have hcompile := compileExpr_gt_ok hlhsCompile hrhsCompile
-- SORRY'D:   have heval :
-- SORRY'D:       evalIRExpr state
-- SORRY'D:         (CompilationModel.compileExpr fields .calldata (.gt lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
-- SORRY'D:           some (SourceSemantics.boolWord
-- SORRY'D:             (SourceSemantics.evalExpr fields runtime rhs % Compiler.Constants.evmModulus <
-- SORRY'D:               SourceSemantics.evalExpr fields runtime lhs % Compiler.Constants.evmModulus)) := by
-- SORRY'D:     simpa [hcompile] using evalIRExpr_gt_of_eval hlhsEval hrhsEval
-- SORRY'D:   rw [heval]
-- SORRY'D:   rw [show SourceSemantics.evalExpr fields runtime (.gt lhs rhs) =
-- SORRY'D:       SourceSemantics.boolWord (decide (SourceSemantics.evalExpr fields runtime rhs <
-- SORRY'D:         SourceSemantics.evalExpr fields runtime lhs)) by rfl]
-- SORRY'D:   simp [Nat.mod_eq_of_lt hlhsLt, Nat.mod_eq_of_lt hrhsLt]

theorem eval_compileExpr_ge_of_compiled {fields : List Field} {runtime : SourceSemantics.RuntimeState}
    {state : IRState} {lhs rhs : Expr} {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs))
    (hlhsLt : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhsLt : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.ge lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.ge lhs rhs)) := by
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsLt' : lhsVal < Compiler.Constants.evmModulus := by
        simpa [hlhsSrc] using hlhsLt
      have hrhsLt' : rhsVal < Compiler.Constants.evmModulus := by
        simpa [hrhsSrc] using hrhsLt
      have heval :=
        eval_compileExpr_ge_raw
          (hlhsCompile := hlhsCompile)
          (hrhsCompile := hrhsCompile)
          (hlhsEval := hlhsEval)
          (hrhsEval := hrhsEval)
      have hsrc :
          SourceSemantics.evalExpr fields runtime (.ge lhs rhs) =
            some (SourceSemantics.boolWord (decide (rhsVal ≤ lhsVal))) := by
        calc
          SourceSemantics.evalExpr fields runtime (.ge lhs rhs)
              = (do
                  let lhs ← SourceSemantics.evalExpr fields runtime lhs
                  let rhs ← SourceSemantics.evalExpr fields runtime rhs
                  pure (SourceSemantics.boolWord (decide (rhs ≤ lhs)))) := by
                    rfl
          _ = some (SourceSemantics.boolWord (decide (rhsVal ≤ lhsVal))) := by
                simp [hlhsSrc, hrhsSrc]
      rw [heval, hsrc]
      simp [hlhsSrc, hrhsSrc, Nat.mod_eq_of_lt hlhsLt', Nat.mod_eq_of_lt hrhsLt']
-- SORRY'D:   have hcompile := compileExpr_ge_ok hlhsCompile hrhsCompile
-- SORRY'D:   have hltEval :
-- SORRY'D:       evalIRExpr state (YulExpr.call "lt" [lhsIR, rhsIR]) =
-- SORRY'D:         some (SourceSemantics.boolWord
-- SORRY'D:           (SourceSemantics.evalExpr fields runtime lhs % Compiler.Constants.evmModulus <
-- SORRY'D:             SourceSemantics.evalExpr fields runtime rhs % Compiler.Constants.evmModulus)) := by
-- SORRY'D:     simpa using evalIRExpr_lt_of_eval hlhsEval hrhsEval
-- SORRY'D:   have hinnerLt :
-- SORRY'D:       SourceSemantics.boolWord
-- SORRY'D:         (SourceSemantics.evalExpr fields runtime lhs % Compiler.Constants.evmModulus <
-- SORRY'D:           SourceSemantics.evalExpr fields runtime rhs % Compiler.Constants.evmModulus) <
-- SORRY'D:         Compiler.Constants.evmModulus :=
-- SORRY'D:     boolWord_lt_evmModulus _
-- SORRY'D:   have heval :
-- SORRY'D:       evalIRExpr state
-- SORRY'D:         (CompilationModel.compileExpr fields .calldata (.ge lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
-- SORRY'D:           some (SourceSemantics.boolWord
-- SORRY'D:             (SourceSemantics.boolWord
-- SORRY'D:               (SourceSemantics.evalExpr fields runtime lhs % Compiler.Constants.evmModulus <
-- SORRY'D:                 SourceSemantics.evalExpr fields runtime rhs % Compiler.Constants.evmModulus) = 0)) := by
-- SORRY'D:     simpa [hcompile] using evalIRExpr_iszero_of_lt hltEval hinnerLt
-- SORRY'D:   rw [heval]
-- SORRY'D:   rw [show SourceSemantics.evalExpr fields runtime (.ge lhs rhs) =
-- SORRY'D:       SourceSemantics.boolWord (decide (SourceSemantics.evalExpr fields runtime rhs ≤
-- SORRY'D:         SourceSemantics.evalExpr fields runtime lhs)) by rfl]
-- SORRY'D:   by_cases hlt : SourceSemantics.evalExpr fields runtime lhs < SourceSemantics.evalExpr fields runtime rhs
-- SORRY'D:   · have hnotle : ¬ SourceSemantics.evalExpr fields runtime rhs ≤
-- SORRY'D:       SourceSemantics.evalExpr fields runtime lhs := Nat.not_le_of_gt hlt
-- SORRY'D:     simp [Nat.mod_eq_of_lt hlhsLt, Nat.mod_eq_of_lt hrhsLt, hlt, hnotle, SourceSemantics.boolWord]
-- SORRY'D:   · have hle : SourceSemantics.evalExpr fields runtime rhs ≤
-- SORRY'D:       SourceSemantics.evalExpr fields runtime lhs := Nat.le_of_not_gt hlt
-- SORRY'D:     simp [Nat.mod_eq_of_lt hlhsLt, Nat.mod_eq_of_lt hrhsLt, hlt, hle, SourceSemantics.boolWord]

theorem eval_compileExpr_le_of_compiled {fields : List Field} {runtime : SourceSemantics.RuntimeState}
    {state : IRState} {lhs rhs : Expr} {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs))
    (hlhsLt : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhsLt : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.le lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.le lhs rhs)) := by
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsLt' : lhsVal < Compiler.Constants.evmModulus := by
        simpa [hlhsSrc] using hlhsLt
      have hrhsLt' : rhsVal < Compiler.Constants.evmModulus := by
        simpa [hrhsSrc] using hrhsLt
      have heval :=
        eval_compileExpr_le_raw
          (hlhsCompile := hlhsCompile)
          (hrhsCompile := hrhsCompile)
          (hlhsEval := hlhsEval)
          (hrhsEval := hrhsEval)
      have hsrc :
          SourceSemantics.evalExpr fields runtime (.le lhs rhs) =
            some (SourceSemantics.boolWord (decide (lhsVal ≤ rhsVal))) := by
        calc
          SourceSemantics.evalExpr fields runtime (.le lhs rhs)
              = (do
                  let lhs ← SourceSemantics.evalExpr fields runtime lhs
                  let rhs ← SourceSemantics.evalExpr fields runtime rhs
                  pure (SourceSemantics.boolWord (decide (lhs ≤ rhs)))) := by
                    rfl
          _ = some (SourceSemantics.boolWord (decide (lhsVal ≤ rhsVal))) := by
                simp [hlhsSrc, hrhsSrc]
      rw [heval, hsrc]
      rw [hlhsSrc, hrhsSrc]
      simpa using congrArg some (boolWord_iszero_gt_eq_le lhsVal rhsVal hlhsLt' hrhsLt')
-- SORRY'D:   have hcompile := compileExpr_le_ok hlhsCompile hrhsCompile
-- SORRY'D:   have hgtEval :
-- SORRY'D:       evalIRExpr state (YulExpr.call "gt" [lhsIR, rhsIR]) =
-- SORRY'D:         some (SourceSemantics.boolWord
-- SORRY'D:           (SourceSemantics.evalExpr fields runtime rhs % Compiler.Constants.evmModulus <
-- SORRY'D:             SourceSemantics.evalExpr fields runtime lhs % Compiler.Constants.evmModulus)) := by
-- SORRY'D:     simpa using evalIRExpr_gt_of_eval hlhsEval hrhsEval
-- SORRY'D:   have hinnerLt :
-- SORRY'D:       SourceSemantics.boolWord
-- SORRY'D:         (SourceSemantics.evalExpr fields runtime rhs % Compiler.Constants.evmModulus <
-- SORRY'D:           SourceSemantics.evalExpr fields runtime lhs % Compiler.Constants.evmModulus) <
-- SORRY'D:         Compiler.Constants.evmModulus :=
-- SORRY'D:     boolWord_lt_evmModulus _
-- SORRY'D:   have heval :
-- SORRY'D:       evalIRExpr state
-- SORRY'D:         (CompilationModel.compileExpr fields .calldata (.le lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
-- SORRY'D:           some (SourceSemantics.boolWord
-- SORRY'D:             (SourceSemantics.boolWord
-- SORRY'D:               (SourceSemantics.evalExpr fields runtime rhs % Compiler.Constants.evmModulus <
-- SORRY'D:                 SourceSemantics.evalExpr fields runtime lhs % Compiler.Constants.evmModulus) = 0)) := by
-- SORRY'D:     simpa [hcompile] using evalIRExpr_iszero_of_lt hgtEval hinnerLt
-- SORRY'D:   rw [heval]
-- SORRY'D:   rw [show SourceSemantics.evalExpr fields runtime (.le lhs rhs) =
-- SORRY'D:       SourceSemantics.boolWord (decide (SourceSemantics.evalExpr fields runtime lhs ≤
-- SORRY'D:         SourceSemantics.evalExpr fields runtime rhs)) by rfl]
-- SORRY'D:   by_cases hgt : SourceSemantics.evalExpr fields runtime rhs < SourceSemantics.evalExpr fields runtime lhs
-- SORRY'D:   · have hnotle : ¬ SourceSemantics.evalExpr fields runtime lhs ≤
-- SORRY'D:       SourceSemantics.evalExpr fields runtime rhs := Nat.not_le_of_gt hgt
-- SORRY'D:     simp [Nat.mod_eq_of_lt hlhsLt, Nat.mod_eq_of_lt hrhsLt, hgt, hnotle, SourceSemantics.boolWord]
-- SORRY'D:   · have hle : SourceSemantics.evalExpr fields runtime lhs ≤
-- SORRY'D:       SourceSemantics.evalExpr fields runtime rhs := Nat.le_of_not_gt hgt
-- SORRY'D:     simp [Nat.mod_eq_of_lt hlhsLt, Nat.mod_eq_of_lt hrhsLt, hgt, hle, SourceSemantics.boolWord]

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
  rcases hexprSrc : SourceSemantics.evalExpr fields runtime expr with _ | exprVal
  · cases hEval : evalIRExpr state exprIR <;> simp [hEval, hexprSrc] at hexprEval
  · have hexprEval' : evalIRExpr state exprIR = some exprVal := by
      cases hEval : evalIRExpr state exprIR with
      | none =>
          simp [hEval, hexprSrc] at hexprEval
      | some val =>
          simp [hEval, hexprSrc] at hexprEval
          simpa [hexprEval] using hEval
    have hexprLt' : exprVal < Compiler.Constants.evmModulus := by
      simpa [hexprSrc] using hexprLt
    rw [hcompile]
    have hiszero :=
      evalIRExpr_iszero_of_lt (heval := hexprEval') (hvalueLt := hexprLt')
    have hsrcNot :
        SourceSemantics.evalExpr fields runtime (.logicalNot expr) =
          some (if exprVal = 0 then 1 else 0) := by
      calc
        SourceSemantics.evalExpr fields runtime (.logicalNot expr)
          = (do
              let value ← SourceSemantics.evalExpr fields runtime expr
              pure (SourceSemantics.boolWord (decide (value = 0)))) := by
                rfl
        _ = some (SourceSemantics.boolWord (decide (exprVal = 0))) := by
              simp [hexprSrc]
        _ = some (if exprVal = 0 then 1 else 0) := by
              simp [boolWord_eq_if]
    calc
      (evalIRExpr state (YulExpr.call "iszero" [exprIR])).bind (fun a => some (some a))
        = some (some (SourceSemantics.boolWord (decide (exprVal = 0)))) := by
            simp [hiszero]
      _ = some (SourceSemantics.evalExpr fields runtime (.logicalNot expr)) := by
            rw [hsrcNot]
            simp [boolWord_eq_if]

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
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' := evalIRExpr_of_sourceEval_some hlhsEval hlhsSrc
      have hrhsEval' := evalIRExpr_of_sourceEval_some hrhsEval hrhsSrc
      have hlhsLt' : lhsVal < Compiler.Constants.evmModulus := by
        simpa [hlhsSrc] using hlhsLt
      have hrhsLt' : rhsVal < Compiler.Constants.evmModulus := by
        simpa [hrhsSrc] using hrhsLt
      have hlhsBool :
          evalIRExpr state (CompilationModel.yulToBool lhsIR) =
            some (SourceSemantics.boolWord (lhsVal ≠ 0)) := by
        simpa using evalIRExpr_yulToBool_of_lt hlhsEval' hlhsLt'
      have hrhsBool :
          evalIRExpr state (CompilationModel.yulToBool rhsIR) =
            some (SourceSemantics.boolWord (rhsVal ≠ 0)) := by
        simpa using evalIRExpr_yulToBool_of_lt hrhsEval' hrhsLt'
      have hcall :
          evalIRExpr state
            (YulExpr.call "and" [CompilationModel.yulToBool lhsIR, CompilationModel.yulToBool rhsIR]) =
              some ((SourceSemantics.boolWord (lhsVal ≠ 0)) &&&
                (SourceSemantics.boolWord (rhsVal ≠ 0))) := by
        simpa only
          [Nat.mod_eq_of_lt (boolWord_lt_evmModulus (decide (lhsVal ≠ 0))),
          Nat.mod_eq_of_lt (boolWord_lt_evmModulus (decide (rhsVal ≠ 0)))] using
          evalIRExpr_and_of_eval hlhsBool hrhsBool
      have heval :
          evalIRExpr state
            (CompilationModel.compileExpr fields .calldata (.logicalAnd lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
              some ((SourceSemantics.boolWord (lhsVal ≠ 0)) &&&
                (SourceSemantics.boolWord (rhsVal ≠ 0))) := by
        simpa [hcompile] using hcall
      have hsrc :
          SourceSemantics.evalExpr fields runtime (.logicalAnd lhs rhs) =
            some (SourceSemantics.boolWord
              (decide (lhsVal != 0) && decide (rhsVal != 0))) := by
        calc
          SourceSemantics.evalExpr fields runtime (.logicalAnd lhs rhs)
              = (do
                  let lhs ← SourceSemantics.evalExpr fields runtime lhs
                  let rhs ← SourceSemantics.evalExpr fields runtime rhs
                  pure (SourceSemantics.boolWord
                    (decide (lhs != 0) && decide (rhs != 0)))) := by
                      rfl
          _ = some (SourceSemantics.boolWord
                (decide (lhsVal != 0) && decide (rhsVal != 0))) := by
                simp [hlhsSrc, hrhsSrc]
      rw [heval, hsrc]
      simp [boolWord_and]
-- SORRY'D:           some ((SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime lhs ≠ 0)) &&&
-- SORRY'D:             (SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime rhs ≠ 0))) := by
-- SORRY'D:     simpa [hcompile] using hcall
-- SORRY'D:   rw [heval]
-- SORRY'D:   congr
-- SORRY'D:   rw [boolWord_and]
-- SORRY'D:   rw [show SourceSemantics.evalExpr fields runtime (.logicalAnd lhs rhs) =
-- SORRY'D:       SourceSemantics.boolWord
-- SORRY'D:         (decide (SourceSemantics.evalExpr fields runtime lhs != 0) &&
-- SORRY'D:           decide (SourceSemantics.evalExpr fields runtime rhs != 0)) by
-- SORRY'D:       rfl]
-- SORRY'D:   by_cases hlhsZero : SourceSemantics.evalExpr fields runtime lhs = 0
-- SORRY'D:   · by_cases hrhsZero : SourceSemantics.evalExpr fields runtime rhs = 0
-- SORRY'D:     · simp [hlhsZero, hrhsZero, SourceSemantics.boolWord]
-- SORRY'D:     · simp [hlhsZero, hrhsZero, SourceSemantics.boolWord]
-- SORRY'D:   · by_cases hrhsZero : SourceSemantics.evalExpr fields runtime rhs = 0
-- SORRY'D:     · simp [hlhsZero, hrhsZero, SourceSemantics.boolWord]
-- SORRY'D:     · simp [hlhsZero, hrhsZero, SourceSemantics.boolWord]

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
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' := evalIRExpr_of_sourceEval_some hlhsEval hlhsSrc
      have hrhsEval' := evalIRExpr_of_sourceEval_some hrhsEval hrhsSrc
      have hlhsLt' : lhsVal < Compiler.Constants.evmModulus := by
        simpa [hlhsSrc] using hlhsLt
      have hrhsLt' : rhsVal < Compiler.Constants.evmModulus := by
        simpa [hrhsSrc] using hrhsLt
      have hlhsBool :
          evalIRExpr state (CompilationModel.yulToBool lhsIR) =
            some (SourceSemantics.boolWord (lhsVal ≠ 0)) := by
        simpa using evalIRExpr_yulToBool_of_lt hlhsEval' hlhsLt'
      have hrhsBool :
          evalIRExpr state (CompilationModel.yulToBool rhsIR) =
            some (SourceSemantics.boolWord (rhsVal ≠ 0)) := by
        simpa using evalIRExpr_yulToBool_of_lt hrhsEval' hrhsLt'
      have hcall :
          evalIRExpr state
            (YulExpr.call "or" [CompilationModel.yulToBool lhsIR, CompilationModel.yulToBool rhsIR]) =
              some ((SourceSemantics.boolWord (lhsVal ≠ 0)) |||
                (SourceSemantics.boolWord (rhsVal ≠ 0))) := by
        simpa only
          [Nat.mod_eq_of_lt (boolWord_lt_evmModulus (decide (lhsVal ≠ 0))),
          Nat.mod_eq_of_lt (boolWord_lt_evmModulus (decide (rhsVal ≠ 0)))] using
          evalIRExpr_or_of_eval hlhsBool hrhsBool
      have heval :
          evalIRExpr state
            (CompilationModel.compileExpr fields .calldata (.logicalOr lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
              some ((SourceSemantics.boolWord (lhsVal ≠ 0)) |||
                (SourceSemantics.boolWord (rhsVal ≠ 0))) := by
        simpa [hcompile] using hcall
      have hsrc :
          SourceSemantics.evalExpr fields runtime (.logicalOr lhs rhs) =
            some (SourceSemantics.boolWord
              (decide (lhsVal != 0) || decide (rhsVal != 0))) := by
        calc
          SourceSemantics.evalExpr fields runtime (.logicalOr lhs rhs)
            = (do
                let lhsVal ← SourceSemantics.evalExpr fields runtime lhs
                let rhsVal ← SourceSemantics.evalExpr fields runtime rhs
                pure (SourceSemantics.boolWord
                  (decide (lhsVal != 0) || decide (rhsVal != 0)))) := by
                  rfl
          _ = some (SourceSemantics.boolWord
                (decide (lhsVal != 0) || decide (rhsVal != 0))) := by
                simp [hlhsSrc, hrhsSrc]
      rw [heval, hsrc]
      simp [boolWord_or]
-- SORRY'D:   have hcompile := compileExpr_logicalOr_ok hlhsCompile hrhsCompile
-- SORRY'D:   have hlhsBool :
-- SORRY'D:       evalIRExpr state (CompilationModel.yulToBool lhsIR) =
-- SORRY'D:         some (SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime lhs ≠ 0)) := by
-- SORRY'D:     simpa using evalIRExpr_yulToBool_of_lt hlhsEval hlhsLt
-- SORRY'D:   have hrhsBool :
-- SORRY'D:       evalIRExpr state (CompilationModel.yulToBool rhsIR) =
-- SORRY'D:         some (SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime rhs ≠ 0)) := by
-- SORRY'D:     simpa using evalIRExpr_yulToBool_of_lt hrhsEval hrhsLt
-- SORRY'D:   have hcall :
-- SORRY'D:       evalIRExpr state
-- SORRY'D:         (YulExpr.call "or" [CompilationModel.yulToBool lhsIR, CompilationModel.yulToBool rhsIR]) =
-- SORRY'D:           some ((SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime lhs ≠ 0)) |||
-- SORRY'D:             (SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime rhs ≠ 0))) := by
-- SORRY'D:     simpa only
-- SORRY'D:       [Nat.mod_eq_of_lt (boolWord_lt_evmModulus (decide (SourceSemantics.evalExpr fields runtime lhs ≠ 0))),
-- SORRY'D:       Nat.mod_eq_of_lt (boolWord_lt_evmModulus (decide (SourceSemantics.evalExpr fields runtime rhs ≠ 0)))] using
-- SORRY'D:       evalIRExpr_or_of_eval hlhsBool hrhsBool
-- SORRY'D:   have heval :
-- SORRY'D:       evalIRExpr state
-- SORRY'D:         (CompilationModel.compileExpr fields .calldata (.logicalOr lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
-- SORRY'D:           some ((SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime lhs ≠ 0)) |||
-- SORRY'D:             (SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime rhs ≠ 0))) := by
-- SORRY'D:     simpa [hcompile] using hcall
-- SORRY'D:   rw [heval]
-- SORRY'D:   congr
-- SORRY'D:   rw [boolWord_or]
-- SORRY'D:   rw [show SourceSemantics.evalExpr fields runtime (.logicalOr lhs rhs) =
-- SORRY'D:       SourceSemantics.boolWord
-- SORRY'D:         (decide (SourceSemantics.evalExpr fields runtime lhs != 0) ||
-- SORRY'D:           decide (SourceSemantics.evalExpr fields runtime rhs != 0)) by
-- SORRY'D:       rfl]
-- SORRY'D:   by_cases hlhsZero : SourceSemantics.evalExpr fields runtime lhs = 0
-- SORRY'D:   · by_cases hrhsZero : SourceSemantics.evalExpr fields runtime rhs = 0
-- SORRY'D:     · simp [hlhsZero, hrhsZero, SourceSemantics.boolWord]
-- SORRY'D:     · simp [hlhsZero, hrhsZero, SourceSemantics.boolWord]
-- SORRY'D:   · by_cases hrhsZero : SourceSemantics.evalExpr fields runtime rhs = 0
-- SORRY'D:     · simp [hlhsZero, hrhsZero, SourceSemantics.boolWord]
-- SORRY'D:     · simp [hlhsZero, hrhsZero, SourceSemantics.boolWord]

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
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' := evalIRExpr_of_sourceEval_some hlhsEval hlhsSrc
      have hrhsEval' := evalIRExpr_of_sourceEval_some hrhsEval hrhsSrc
      have heval :
          evalIRExpr state
            (CompilationModel.compileExpr fields .calldata (.add lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
              some ((lhsVal + rhsVal) % Compiler.Constants.evmModulus) := by
        simpa [hcompile] using evalIRExpr_add_of_eval hlhsEval' hrhsEval'
      have hsrc := evalExpr_add_of_values hlhsSrc hrhsSrc
      rw [heval, hsrc]
      simp [HAdd.hAdd, Verity.Core.Uint256.add, Verity.Core.Uint256.ofNat,
        Verity.Core.Uint256.modulus, Compiler.Constants.evmModulus,
        Verity.Core.UINT256_MODULUS]
      simpa [Add.add] using (Nat.add_mod lhsVal rhsVal Compiler.Constants.evmModulus).symm
-- SORRY'D:   have hcompile := compileExpr_add_ok hlhsCompile hrhsCompile
-- SORRY'D:   have heval :
-- SORRY'D:       evalIRExpr state
-- SORRY'D:         (CompilationModel.compileExpr fields .calldata (.add lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
-- SORRY'D:           some ((SourceSemantics.evalExpr fields runtime lhs +
-- SORRY'D:             SourceSemantics.evalExpr fields runtime rhs) % Compiler.Constants.evmModulus) := by
-- SORRY'D:     simpa [hcompile] using evalIRExpr_add_of_eval hlhsEval hrhsEval
-- SORRY'D:   rw [heval]
-- SORRY'D:   refine congrArg some ?_
-- SORRY'D:   change
-- SORRY'D:     ((SourceSemantics.evalExpr fields runtime lhs + SourceSemantics.evalExpr fields runtime rhs) %
-- SORRY'D:       Compiler.Constants.evmModulus) =
-- SORRY'D:     (((SourceSemantics.evalExpr fields runtime lhs : Verity.Core.Uint256) +
-- SORRY'D:       (SourceSemantics.evalExpr fields runtime rhs : Verity.Core.Uint256)) : Verity.Core.Uint256).val
-- SORRY'D:   rw [Nat.add_mod]
-- SORRY'D:   simp [HAdd.hAdd, Verity.Core.Uint256.add, Verity.Core.Uint256.ofNat,
-- SORRY'D:     Verity.Core.Uint256.modulus, Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS]

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
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' := evalIRExpr_of_sourceEval_some hlhsEval hlhsSrc
      have hrhsEval' := evalIRExpr_of_sourceEval_some hrhsEval hrhsSrc
      have heval :
          evalIRExpr state
            (CompilationModel.compileExpr fields .calldata (.mul lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
              some ((lhsVal * rhsVal) % Compiler.Constants.evmModulus) := by
        simpa [hcompile] using evalIRExpr_mul_of_eval hlhsEval' hrhsEval'
      have hsrc := evalExpr_mul_of_values hlhsSrc hrhsSrc
      rw [heval, hsrc]
      simp [HMul.hMul, Verity.Core.Uint256.mul, Verity.Core.Uint256.ofNat,
        Verity.Core.Uint256.modulus, Compiler.Constants.evmModulus,
        Verity.Core.UINT256_MODULUS]
      simpa [Mul.mul] using (Nat.mul_mod lhsVal rhsVal Compiler.Constants.evmModulus).symm
-- SORRY'D:   have hcompile := compileExpr_mul_ok hlhsCompile hrhsCompile
-- SORRY'D:   have heval :
-- SORRY'D:       evalIRExpr state
-- SORRY'D:         (CompilationModel.compileExpr fields .calldata (.mul lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
-- SORRY'D:           some ((SourceSemantics.evalExpr fields runtime lhs *
-- SORRY'D:             SourceSemantics.evalExpr fields runtime rhs) % Compiler.Constants.evmModulus) := by
-- SORRY'D:     simpa [hcompile] using evalIRExpr_mul_of_eval hlhsEval hrhsEval
-- SORRY'D:   rw [heval]
-- SORRY'D:   refine congrArg some ?_
-- SORRY'D:   change
-- SORRY'D:     ((SourceSemantics.evalExpr fields runtime lhs * SourceSemantics.evalExpr fields runtime rhs) %
-- SORRY'D:       Compiler.Constants.evmModulus) =
-- SORRY'D:     (((SourceSemantics.evalExpr fields runtime lhs : Verity.Core.Uint256) *
-- SORRY'D:       (SourceSemantics.evalExpr fields runtime rhs : Verity.Core.Uint256)) : Verity.Core.Uint256).val
-- SORRY'D:   rw [Nat.mul_mod]
-- SORRY'D:   simp [HMul.hMul, Verity.Core.Uint256.mul, Verity.Core.Uint256.ofNat,
-- SORRY'D:     Verity.Core.Uint256.modulus, Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS]

-- SORRY'D: /-- Bridge `Nat` values already known to be in-range to their `Uint256` coercion. -/
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
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' := evalIRExpr_of_sourceEval_some hlhsEval hlhsSrc
      have hrhsEval' := evalIRExpr_of_sourceEval_some hrhsEval hrhsSrc
      have hlhsLt' : lhsVal < Compiler.Constants.evmModulus := by
        simpa [hlhsSrc] using hlhsLt
      have hrhsLt' : rhsVal < Compiler.Constants.evmModulus := by
        simpa [hrhsSrc] using hrhsLt
      have heval :
          evalIRExpr state
            (CompilationModel.compileExpr fields .calldata (.div lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
              some (if rhsVal % Compiler.Constants.evmModulus = 0 then 0 else
                (lhsVal % Compiler.Constants.evmModulus) / (rhsVal % Compiler.Constants.evmModulus)) := by
        simpa [hcompile] using evalIRExpr_div_of_eval hlhsEval' hrhsEval'
      have hsrc := evalExpr_div_of_values hlhsSrc hrhsSrc
      rw [heval]
      rw [hsrc]
      rw [uint256_div_val_eq hlhsLt' hrhsLt']
      simp [Nat.mod_eq_of_lt hlhsLt', Nat.mod_eq_of_lt hrhsLt']
-- SORRY'D:   have hcompile := compileExpr_div_ok hlhsCompile hrhsCompile
-- SORRY'D:   have heval :
-- SORRY'D:       evalIRExpr state
-- SORRY'D:         (CompilationModel.compileExpr fields .calldata (.div lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
-- SORRY'D:           some (if SourceSemantics.evalExpr fields runtime rhs % Compiler.Constants.evmModulus = 0 then 0
-- SORRY'D:             else
-- SORRY'D:               (SourceSemantics.evalExpr fields runtime lhs % Compiler.Constants.evmModulus) /
-- SORRY'D:                 (SourceSemantics.evalExpr fields runtime rhs % Compiler.Constants.evmModulus)) := by
-- SORRY'D:     simpa [hcompile] using evalIRExpr_div_of_eval hlhsEval hrhsEval
-- SORRY'D:   rw [heval]
-- SORRY'D:   rw [show SourceSemantics.evalExpr fields runtime (.div lhs rhs) =
-- SORRY'D:       (((SourceSemantics.evalExpr fields runtime lhs : Verity.Core.Uint256) /
-- SORRY'D:         (SourceSemantics.evalExpr fields runtime rhs : Verity.Core.Uint256)) : Verity.Core.Uint256).val by
-- SORRY'D:       rfl]
-- SORRY'D:   rw [uint256_div_val_eq hlhsLt hrhsLt]
-- SORRY'D:   simp [Nat.mod_eq_of_lt hlhsLt, Nat.mod_eq_of_lt hrhsLt]

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
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' := evalIRExpr_of_sourceEval_some hlhsEval hlhsSrc
      have hrhsEval' := evalIRExpr_of_sourceEval_some hrhsEval hrhsSrc
      have hlhsLt' : lhsVal < Compiler.Constants.evmModulus := by
        simpa [hlhsSrc] using hlhsLt
      have hrhsLt' : rhsVal < Compiler.Constants.evmModulus := by
        simpa [hrhsSrc] using hrhsLt
      have heval :
          evalIRExpr state
            (CompilationModel.compileExpr fields .calldata (.sub lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
              some ((Compiler.Constants.evmModulus +
                (lhsVal % Compiler.Constants.evmModulus) -
                (rhsVal % Compiler.Constants.evmModulus)) % Compiler.Constants.evmModulus) := by
        simpa [hcompile] using evalIRExpr_sub_of_eval hlhsEval' hrhsEval'
      have hsrc := evalExpr_sub_of_values hlhsSrc hrhsSrc
      rw [heval]
      rw [hsrc]
      rw [uint256_sub_val_eq hlhsLt' hrhsLt']
      simp [Nat.mod_eq_of_lt hlhsLt', Nat.mod_eq_of_lt hrhsLt']
-- SORRY'D:   have hcompile := compileExpr_sub_ok hlhsCompile hrhsCompile
-- SORRY'D:   have heval :
-- SORRY'D:       evalIRExpr state
-- SORRY'D:         (CompilationModel.compileExpr fields .calldata (.sub lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
-- SORRY'D:           some ((Compiler.Constants.evmModulus +
-- SORRY'D:             (SourceSemantics.evalExpr fields runtime lhs % Compiler.Constants.evmModulus) -
-- SORRY'D:             (SourceSemantics.evalExpr fields runtime rhs % Compiler.Constants.evmModulus)) %
-- SORRY'D:               Compiler.Constants.evmModulus) := by
-- SORRY'D:     simpa [hcompile] using evalIRExpr_sub_of_eval hlhsEval hrhsEval
-- SORRY'D:   rw [heval]
-- SORRY'D:   rw [show SourceSemantics.evalExpr fields runtime (.sub lhs rhs) =
-- SORRY'D:       (((SourceSemantics.evalExpr fields runtime lhs : Verity.Core.Uint256) -
-- SORRY'D:         (SourceSemantics.evalExpr fields runtime rhs : Verity.Core.Uint256)) : Verity.Core.Uint256).val by
-- SORRY'D:       rfl]
-- SORRY'D:   rw [uint256_sub_val_eq hlhsLt hrhsLt]
-- SORRY'D:   simp [Nat.mod_eq_of_lt hlhsLt, Nat.mod_eq_of_lt hrhsLt]

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
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' := evalIRExpr_of_sourceEval_some hlhsEval hlhsSrc
      have hrhsEval' := evalIRExpr_of_sourceEval_some hrhsEval hrhsSrc
      have hlhsLt' : lhsVal < Compiler.Constants.evmModulus := by
        simpa [hlhsSrc] using hlhsLt
      have hrhsLt' : rhsVal < Compiler.Constants.evmModulus := by
        simpa [hrhsSrc] using hrhsLt
      have heval :
          evalIRExpr state
            (CompilationModel.compileExpr fields .calldata (.mod lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
              some (if rhsVal % Compiler.Constants.evmModulus = 0 then 0 else
                (lhsVal % Compiler.Constants.evmModulus) % (rhsVal % Compiler.Constants.evmModulus)) := by
        simpa [hcompile] using evalIRExpr_mod_of_eval hlhsEval' hrhsEval'
      have hsrc := evalExpr_mod_of_values hlhsSrc hrhsSrc
      rw [heval]
      rw [hsrc]
      rw [uint256_mod_val_eq hlhsLt' hrhsLt']
      simp [Nat.mod_eq_of_lt hlhsLt', Nat.mod_eq_of_lt hrhsLt']
-- SORRY'D:   have hcompile := compileExpr_mod_ok hlhsCompile hrhsCompile
-- SORRY'D:   have heval :
-- SORRY'D:       evalIRExpr state
-- SORRY'D:         (CompilationModel.compileExpr fields .calldata (.mod lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
-- SORRY'D:           some (if SourceSemantics.evalExpr fields runtime rhs % Compiler.Constants.evmModulus = 0 then 0
-- SORRY'D:             else
-- SORRY'D:               (SourceSemantics.evalExpr fields runtime lhs % Compiler.Constants.evmModulus) %
-- SORRY'D:                 (SourceSemantics.evalExpr fields runtime rhs % Compiler.Constants.evmModulus)) := by
-- SORRY'D:     simpa [hcompile] using evalIRExpr_mod_of_eval hlhsEval hrhsEval
-- SORRY'D:   rw [heval]
-- SORRY'D:   rw [show SourceSemantics.evalExpr fields runtime (.mod lhs rhs) =
-- SORRY'D:       (((SourceSemantics.evalExpr fields runtime lhs : Verity.Core.Uint256) %
-- SORRY'D:         (SourceSemantics.evalExpr fields runtime rhs : Verity.Core.Uint256)) : Verity.Core.Uint256).val by
-- SORRY'D:       rfl]
-- SORRY'D:   rw [uint256_mod_val_eq hlhsLt hrhsLt]
-- SORRY'D:   simp [Nat.mod_eq_of_lt hlhsLt, Nat.mod_eq_of_lt hrhsLt]

private theorem evalExpr_bitAnd_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {lhs rhs : Expr}
    {lhsVal rhsVal : Nat}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs = some lhsVal)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs = some rhsVal) :
    SourceSemantics.evalExpr fields runtime (.bitAnd lhs rhs) =
      some ((Verity.Core.Uint256.and (lhsVal : Verity.Core.Uint256)
        (rhsVal : Verity.Core.Uint256)).val) := by
  calc
    SourceSemantics.evalExpr fields runtime (.bitAnd lhs rhs)
        = (do
            let l ← SourceSemantics.evalExpr fields runtime lhs
            let r ← SourceSemantics.evalExpr fields runtime rhs
            pure (Verity.Core.Uint256.and l r).val) := by rfl
    _ = some ((Verity.Core.Uint256.and (lhsVal : Verity.Core.Uint256)
          (rhsVal : Verity.Core.Uint256)).val) := by simp [hlhs, hrhs]

private theorem evalExpr_bitOr_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {lhs rhs : Expr}
    {lhsVal rhsVal : Nat}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs = some lhsVal)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs = some rhsVal) :
    SourceSemantics.evalExpr fields runtime (.bitOr lhs rhs) =
      some ((Verity.Core.Uint256.or (lhsVal : Verity.Core.Uint256)
        (rhsVal : Verity.Core.Uint256)).val) := by
  calc
    SourceSemantics.evalExpr fields runtime (.bitOr lhs rhs)
        = (do
            let l ← SourceSemantics.evalExpr fields runtime lhs
            let r ← SourceSemantics.evalExpr fields runtime rhs
            pure (Verity.Core.Uint256.or l r).val) := by rfl
    _ = some ((Verity.Core.Uint256.or (lhsVal : Verity.Core.Uint256)
          (rhsVal : Verity.Core.Uint256)).val) := by simp [hlhs, hrhs]

private theorem evalExpr_bitXor_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {lhs rhs : Expr}
    {lhsVal rhsVal : Nat}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs = some lhsVal)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs = some rhsVal) :
    SourceSemantics.evalExpr fields runtime (.bitXor lhs rhs) =
      some ((Verity.Core.Uint256.xor (lhsVal : Verity.Core.Uint256)
        (rhsVal : Verity.Core.Uint256)).val) := by
  calc
    SourceSemantics.evalExpr fields runtime (.bitXor lhs rhs)
        = (do
            let l ← SourceSemantics.evalExpr fields runtime lhs
            let r ← SourceSemantics.evalExpr fields runtime rhs
            pure (Verity.Core.Uint256.xor l r).val) := by rfl
    _ = some ((Verity.Core.Uint256.xor (lhsVal : Verity.Core.Uint256)
          (rhsVal : Verity.Core.Uint256)).val) := by simp [hlhs, hrhs]

private theorem evalExpr_bitNot_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {expr : Expr}
    {val : Nat}
    (hexpr : SourceSemantics.evalExpr fields runtime expr = some val) :
    SourceSemantics.evalExpr fields runtime (.bitNot expr) =
      some ((Verity.Core.Uint256.not (val : Verity.Core.Uint256)).val) := by
  calc
    SourceSemantics.evalExpr fields runtime (.bitNot expr)
        = (do
            let v ← SourceSemantics.evalExpr fields runtime expr
            pure (Verity.Core.Uint256.not v).val) := by rfl
    _ = some ((Verity.Core.Uint256.not (val : Verity.Core.Uint256)).val) := by simp [hexpr]

theorem eval_compileExpr_bitAnd_of_compiled
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
      (CompilationModel.compileExpr fields .calldata (.bitAnd lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.bitAnd lhs rhs)) := by
  have hcompile := compileExpr_bitAnd_ok hlhsCompile hrhsCompile
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' := evalIRExpr_of_sourceEval_some hlhsEval hlhsSrc
      have hrhsEval' := evalIRExpr_of_sourceEval_some hrhsEval hrhsSrc
      have hlhsLt' : lhsVal < Compiler.Constants.evmModulus := by simpa [hlhsSrc] using hlhsLt
      have hrhsLt' : rhsVal < Compiler.Constants.evmModulus := by simpa [hrhsSrc] using hrhsLt
      have heval :
          evalIRExpr state
            (CompilationModel.compileExpr fields .calldata (.bitAnd lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
              some ((lhsVal % Compiler.Constants.evmModulus) &&& (rhsVal % Compiler.Constants.evmModulus)) := by
        simpa [hcompile] using evalIRExpr_and_of_eval hlhsEval' hrhsEval'
      have hsrc := evalExpr_bitAnd_of_values hlhsSrc hrhsSrc
      rw [heval, hsrc]
      simp only [Verity.Core.Uint256.and, Verity.Core.Uint256.ofNat,
        Verity.Core.Uint256.modulus, Compiler.Constants.evmModulus,
        Verity.Core.UINT256_MODULUS,
        Nat.mod_eq_of_lt hlhsLt', Nat.mod_eq_of_lt hrhsLt']
      have hresLt : Nat.land lhsVal rhsVal < 2 ^ 256 := Nat.and_lt_two_pow lhsVal
          (show rhsVal < 2 ^ 256 by rwa [show (2 : Nat) ^ 256 = Compiler.Constants.evmModulus from rfl])
      show some (some (lhsVal.land rhsVal)) = some (some (lhsVal.land rhsVal % _))
      rw [Nat.mod_eq_of_lt hresLt]

theorem eval_compileExpr_bitOr_of_compiled
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
      (CompilationModel.compileExpr fields .calldata (.bitOr lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.bitOr lhs rhs)) := by
  have hcompile := compileExpr_bitOr_ok hlhsCompile hrhsCompile
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' := evalIRExpr_of_sourceEval_some hlhsEval hlhsSrc
      have hrhsEval' := evalIRExpr_of_sourceEval_some hrhsEval hrhsSrc
      have hlhsLt' : lhsVal < Compiler.Constants.evmModulus := by simpa [hlhsSrc] using hlhsLt
      have hrhsLt' : rhsVal < Compiler.Constants.evmModulus := by simpa [hrhsSrc] using hrhsLt
      have heval :
          evalIRExpr state
            (CompilationModel.compileExpr fields .calldata (.bitOr lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
              some ((lhsVal % Compiler.Constants.evmModulus) ||| (rhsVal % Compiler.Constants.evmModulus)) := by
        simpa [hcompile] using evalIRExpr_or_of_eval hlhsEval' hrhsEval'
      have hsrc := evalExpr_bitOr_of_values hlhsSrc hrhsSrc
      rw [heval, hsrc]
      simp only [Verity.Core.Uint256.or, Verity.Core.Uint256.ofNat,
        Verity.Core.Uint256.modulus, Compiler.Constants.evmModulus,
        Verity.Core.UINT256_MODULUS,
        Nat.mod_eq_of_lt hlhsLt', Nat.mod_eq_of_lt hrhsLt']
      have hresLt : Nat.lor lhsVal rhsVal < 2 ^ 256 := Nat.or_lt_two_pow
          (show lhsVal < 2 ^ 256 by rwa [show (2 : Nat) ^ 256 = Compiler.Constants.evmModulus from rfl])
          (show rhsVal < 2 ^ 256 by rwa [show (2 : Nat) ^ 256 = Compiler.Constants.evmModulus from rfl])
      show some (some (lhsVal.lor rhsVal)) = some (some (lhsVal.lor rhsVal % _))
      rw [Nat.mod_eq_of_lt hresLt]

theorem eval_compileExpr_bitXor_of_compiled
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
      (CompilationModel.compileExpr fields .calldata (.bitXor lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.bitXor lhs rhs)) := by
  have hcompile := compileExpr_bitXor_ok hlhsCompile hrhsCompile
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' := evalIRExpr_of_sourceEval_some hlhsEval hlhsSrc
      have hrhsEval' := evalIRExpr_of_sourceEval_some hrhsEval hrhsSrc
      have hlhsLt' : lhsVal < Compiler.Constants.evmModulus := by simpa [hlhsSrc] using hlhsLt
      have hrhsLt' : rhsVal < Compiler.Constants.evmModulus := by simpa [hrhsSrc] using hrhsLt
      have heval :
          evalIRExpr state
            (CompilationModel.compileExpr fields .calldata (.bitXor lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
              some (Nat.xor (lhsVal % Compiler.Constants.evmModulus) (rhsVal % Compiler.Constants.evmModulus)) := by
        simpa [hcompile] using evalIRExpr_xor_of_eval hlhsEval' hrhsEval'
      have hsrc := evalExpr_bitXor_of_values hlhsSrc hrhsSrc
      rw [heval, hsrc]
      simp only [Verity.Core.Uint256.xor, Verity.Core.Uint256.ofNat,
        Verity.Core.Uint256.modulus, Compiler.Constants.evmModulus,
        Verity.Core.UINT256_MODULUS,
        Nat.mod_eq_of_lt hlhsLt', Nat.mod_eq_of_lt hrhsLt']
      have hresLt : Nat.xor lhsVal rhsVal < 2 ^ 256 := Nat.xor_lt_two_pow
          (show lhsVal < 2 ^ 256 by rwa [show (2 : Nat) ^ 256 = Compiler.Constants.evmModulus from rfl])
          (show rhsVal < 2 ^ 256 by rwa [show (2 : Nat) ^ 256 = Compiler.Constants.evmModulus from rfl])
      show some (some (Nat.xor lhsVal rhsVal)) = some (some (Nat.xor lhsVal rhsVal % _))
      rw [Nat.mod_eq_of_lt hresLt]

theorem eval_compileExpr_bitNot_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {expr : Expr}
    {exprIR : YulExpr}
    (hexprCompile : CompilationModel.compileExpr fields .calldata expr = Except.ok exprIR)
    (hexprEval : evalIRExpr state exprIR = some (SourceSemantics.evalExpr fields runtime expr))
    (hexprLt : SourceSemantics.evalExpr fields runtime expr < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.bitNot expr) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.bitNot expr)) := by
  have hcompile := compileExpr_bitNot_ok hexprCompile
  rcases hexprSrc : SourceSemantics.evalExpr fields runtime expr with _ | val
  · cases hEval : evalIRExpr state exprIR <;> simp [hEval, hexprSrc] at hexprEval
  · have hexprEval' := evalIRExpr_of_sourceEval_some hexprEval hexprSrc
    have hvalLt : val < Compiler.Constants.evmModulus := by simpa [hexprSrc] using hexprLt
    have heval :
        evalIRExpr state
          (CompilationModel.compileExpr fields .calldata (.bitNot expr) |>.toOption.getD (YulExpr.lit 0)) =
            some (Nat.xor (val % Compiler.Constants.evmModulus) (Compiler.Constants.evmModulus - 1)) := by
      simpa [hcompile] using evalIRExpr_not_of_eval hexprEval'
    have hsrc := evalExpr_bitNot_of_values hexprSrc
    -- Need to equate IR result (val ^^^ (evmModulus - 1)) with source result (Uint256.not (ofNat val)).val
    have hvalLt256 : val < 2 ^ 256 := by rwa [show (2 : Nat) ^ 256 = Compiler.Constants.evmModulus from rfl]
    -- Prove the bitwise NOT identity: xor val (2^256-1) = 2^256-1-val
    have hxor_eq : Nat.xor val (2 ^ 256 - 1) = 2 ^ 256 - 1 - val := by
      have key : (BitVec.ofNat 256 val ^^^ BitVec.allOnes 256).toNat = 2 ^ 256 - 1 - val := by
        rw [BitVec.xor_allOnes]
        simp only [BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvalLt256]
      have lhs_eq : Nat.xor val (2 ^ 256 - 1) =
          (BitVec.ofNat 256 val ^^^ BitVec.allOnes 256).toNat := by
        simp only [BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvalLt256,
          BitVec.toNat_allOnes]
        rfl
      rw [lhs_eq, key]
    -- Now combine: IR evaluates to xor val (evmModulus-1), source evaluates to Uint256.not
    rw [heval, hsrc]
    -- Simplify: val % evmModulus → val, unfold Uint256.not/ofNat/MAX_UINT256 on RHS
    simp only [Nat.mod_eq_of_lt hvalLt,
      Verity.Core.Uint256.not, Verity.Core.Uint256.val_ofNat,
      Verity.Core.MAX_UINT256, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]
    -- Goal: some (some (Nat.xor val (2^256-1))) = some (some ((2^256-1-val) % 2^256))
    rw [show Compiler.Constants.evmModulus = 2 ^ 256 from rfl, hxor_eq,
      Nat.mod_eq_of_lt (by omega : 2 ^ 256 - 1 - val < 2 ^ 256)]
    simp

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
  | bitAnd hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "and" [lhsIR, rhsIR], compileExpr_bitAnd_ok hlhs hrhs⟩
  | bitOr hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "or" [lhsIR, rhsIR], compileExpr_bitOr_ok hlhs hrhs⟩
  | bitXor hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "xor" [lhsIR, rhsIR], compileExpr_bitXor_ok hlhs hrhs⟩
  | bitNot h ih =>
      rename_i expr
      rcases ih with ⟨exprIR, hexpr⟩
      exact ⟨YulExpr.call "not" [exprIR], compileExpr_bitNot_ok hexpr⟩

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
  | bitAnd hL hR ihL ihR =>
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
      exact eval_compileExpr_bitAnd_of_compiled hlhs hrhs
        hEvalL hEvalR
        (evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime)
  | bitOr hL hR ihL ihR =>
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
      exact eval_compileExpr_bitOr_of_compiled hlhs hrhs
        hEvalL hEvalR
        (evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime)
  | bitXor hL hR ihL ihR =>
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
      exact eval_compileExpr_bitXor_of_compiled hlhs hrhs
        hEvalL hEvalR
        (evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime)
  | bitNot h ih =>
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
      exact eval_compileExpr_bitNot_of_compiled hexpr
        hEval
        (evalExpr_lt_evmModulus_core_onExpr h hexact' hbounded hpresent' hruntime)

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
      change SourceSemantics.wordNormalize value < Compiler.Constants.evmModulus
      exact wordNormalize_lt_evmModulus value
  | param name =>
      change SourceSemantics.lookupValue runtime.bindings name < Compiler.Constants.evmModulus
      exact hbounded name
  | localVar name =>
      change SourceSemantics.lookupValue runtime.bindings name < Compiler.Constants.evmModulus
      exact hbounded name
  | caller =>
      change runtime.world.sender.val < Compiler.Constants.evmModulus
      exact Nat.lt_trans runtime.world.sender.isLt (by decide)
  | contractAddress =>
      change runtime.world.thisAddress.val < Compiler.Constants.evmModulus
      exact Nat.lt_trans runtime.world.thisAddress.isLt (by decide)
  | msgValue =>
      change runtime.world.msgValue.val < Compiler.Constants.evmModulus
      exact runtime.world.msgValue.isLt
  | blockTimestamp =>
      change runtime.world.blockTimestamp.val < Compiler.Constants.evmModulus
      exact runtime.world.blockTimestamp.isLt
  | blockNumber =>
      change runtime.world.blockNumber.val < Compiler.Constants.evmModulus
      exact runtime.world.blockNumber.isLt
  | chainid =>
      change runtime.world.chainId.val < Compiler.Constants.evmModulus
      exact runtime.world.chainId.isLt
  | @add lhs rhs _ _ _ _ =>
      show (do let l : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime lhs
               let r : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime rhs
               pure (l + r).val) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · exact (Verity.Core.Uint256.ofNat lVal + Verity.Core.Uint256.ofNat rVal).isLt
  | @sub lhs rhs _ _ _ _ =>
      show (do let l : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime lhs
               let r : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime rhs
               pure (l - r).val) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · exact (Verity.Core.Uint256.ofNat lVal - Verity.Core.Uint256.ofNat rVal).isLt
  | @mul lhs rhs _ _ _ _ =>
      show (do let l : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime lhs
               let r : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime rhs
               pure (l * r).val) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · exact (Verity.Core.Uint256.ofNat lVal * Verity.Core.Uint256.ofNat rVal).isLt
  | @div lhs rhs _ _ _ _ =>
      show (do let l : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime lhs
               let r : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime rhs
               pure (l / r).val) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · exact (Verity.Core.Uint256.ofNat lVal / Verity.Core.Uint256.ofNat rVal).isLt
  | @mod lhs rhs _ _ _ _ =>
      show (do let l : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime lhs
               let r : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime rhs
               pure (l % r).val) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · exact (Verity.Core.Uint256.ofNat lVal % Verity.Core.Uint256.ofNat rVal).isLt
  | @eq lhs rhs _ _ _ _ =>
      show (do let lv ← SourceSemantics.evalExpr fields runtime lhs
               let rv ← SourceSemantics.evalExpr fields runtime rhs
               pure (SourceSemantics.boolWord (decide (lv = rv)))) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · exact boolWord_lt_evmModulus _
  | @lt lhs rhs _ _ _ _ =>
      show (do let lv ← SourceSemantics.evalExpr fields runtime lhs
               let rv ← SourceSemantics.evalExpr fields runtime rhs
               pure (SourceSemantics.boolWord (decide (lv < rv)))) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · exact boolWord_lt_evmModulus _
  | @gt lhs rhs _ _ _ _ =>
      show (do let lv ← SourceSemantics.evalExpr fields runtime lhs
               let rv ← SourceSemantics.evalExpr fields runtime rhs
               pure (SourceSemantics.boolWord (decide (rv < lv)))) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · exact boolWord_lt_evmModulus _
  | @ge lhs rhs _ _ _ _ =>
      show (do let lv ← SourceSemantics.evalExpr fields runtime lhs
               let rv ← SourceSemantics.evalExpr fields runtime rhs
               pure (SourceSemantics.boolWord (decide (rv ≤ lv)))) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · exact boolWord_lt_evmModulus _
  | @le lhs rhs _ _ _ _ =>
      show (do let lv ← SourceSemantics.evalExpr fields runtime lhs
               let rv ← SourceSemantics.evalExpr fields runtime rhs
               pure (SourceSemantics.boolWord (decide (lv ≤ rv)))) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · exact boolWord_lt_evmModulus _
  | @logicalNot subexpr _ _ =>
      show (do let value ← SourceSemantics.evalExpr fields runtime subexpr
               pure (SourceSemantics.boolWord (decide (value = 0)))) < _
      rcases SourceSemantics.evalExpr fields runtime subexpr with _ | val
      · trivial
      · exact boolWord_lt_evmModulus _
  | @logicalAnd lhs rhs _ _ _ _ =>
      show (do let lv ← SourceSemantics.evalExpr fields runtime lhs
               let rv ← SourceSemantics.evalExpr fields runtime rhs
               pure (SourceSemantics.boolWord (decide (lv != 0) && decide (rv != 0)))) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · exact boolWord_lt_evmModulus _
  | @logicalOr lhs rhs _ _ _ _ =>
      show (do let lv ← SourceSemantics.evalExpr fields runtime lhs
               let rv ← SourceSemantics.evalExpr fields runtime rhs
               pure (SourceSemantics.boolWord (decide (lv != 0) || decide (rv != 0)))) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · exact boolWord_lt_evmModulus _
  | @bitAnd lhs rhs _ _ _ _ =>
      show (do let l : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime lhs
               let r : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime rhs
               pure (Verity.Core.Uint256.and l r).val) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · exact (Verity.Core.Uint256.and (Verity.Core.Uint256.ofNat lVal) (Verity.Core.Uint256.ofNat rVal)).isLt
  | @bitOr lhs rhs _ _ _ _ =>
      show (do let l : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime lhs
               let r : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime rhs
               pure (Verity.Core.Uint256.or l r).val) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · exact (Verity.Core.Uint256.or (Verity.Core.Uint256.ofNat lVal) (Verity.Core.Uint256.ofNat rVal)).isLt
  | @bitXor lhs rhs _ _ _ _ =>
      show (do let l : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime lhs
               let r : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime rhs
               pure (Verity.Core.Uint256.xor l r).val) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · exact (Verity.Core.Uint256.xor (Verity.Core.Uint256.ofNat lVal) (Verity.Core.Uint256.ofNat rVal)).isLt
  | @bitNot subexpr _ _ =>
      show (do let v : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime subexpr
               pure (Verity.Core.Uint256.not v).val) < _
      rcases SourceSemantics.evalExpr fields runtime subexpr with _ | val
      · trivial
      · exact (Verity.Core.Uint256.not (Verity.Core.Uint256.ofNat val)).isLt
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
  | bitAnd hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "and" [lhsIR, rhsIR]], by
        rw [CompilationModel.compileRequireFailCond, compileExpr_bitAnd_ok hlhs hrhs]
        all_goals
          try rfl
          try
            intro a b hEq
            cases hEq⟩
  | bitOr hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "or" [lhsIR, rhsIR]], by
        rw [CompilationModel.compileRequireFailCond, compileExpr_bitOr_ok hlhs hrhs]
        all_goals
          try rfl
          try
            intro a b hEq
            cases hEq⟩
  | bitXor hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "xor" [lhsIR, rhsIR]], by
        rw [CompilationModel.compileRequireFailCond, compileExpr_bitXor_ok hlhs hrhs]
        all_goals
          try rfl
          try
            intro a b hEq
            cases hEq⟩
  | bitNot h =>
      rename_i expr
      rcases compileExpr_core_ok (fields := fields) h with ⟨exprIR, hexpr⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "not" [exprIR]], by
        rw [CompilationModel.compileRequireFailCond, compileExpr_bitNot_ok hexpr]
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
        some (SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime cond = some 0)) := by
  -- Helper for the iszero cases: extract Nat from the monadic Option wrapper
  let finishIszeroEval {expr : Expr} (h : ExprCompileCore expr)
      (hexactExpr : bindingsExactlyMatchIRVarsOnExpr expr runtime.bindings state)
      (hpresentExpr : exprBoundNamesPresent expr runtime.bindings)
      {exprIR : YulExpr}
      (hexpr : CompilationModel.compileExpr fields .calldata expr = Except.ok exprIR) :
      evalIRExpr state (YulExpr.call "iszero" [exprIR]) =
        some (SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime expr = some 0)) := by
    -- eval_compileExpr_core_onExpr gives (elaborated):
    --   (do let a ← evalIRExpr state exprIR; pure (some a)) = some (evalExpr ...)
    have heval := eval_compileExpr_core_onExpr h hexactExpr hbounded hpresentExpr hruntime
    rw [hexpr] at heval
    simp [Except.toOption] at heval
    -- heval : (evalIRExpr state exprIR).bind (fun a => some (some a)) = some (evalExpr ...)
    -- Case split on evalIRExpr to extract the Nat value
    rcases hIR : evalIRExpr state exprIR with _ | val
    · simp [hIR, Option.bind] at heval
    · simp [hIR, Option.bind] at heval
      -- heval : some val = evalExpr fields runtime expr, i.e., evalExpr = some val
      have hEvalSrc : SourceSemantics.evalExpr fields runtime expr = some val := heval.symm
      -- Boundedness: evalExpr < some evmModulus
      have hlt := evalExpr_lt_evmModulus_core_onExpr h hexactExpr hbounded hpresentExpr hruntime
      rw [hEvalSrc] at hlt
      simp at hlt
      -- Apply evalIRExpr_iszero_of_lt
      have hiszero := evalIRExpr_iszero_of_lt hIR hlt
      -- hiszero : ... = some (boolWord (val = 0))
      -- goal : ... = some (boolWord (evalExpr ... = some 0))
      -- Since evalExpr = some val, (evalExpr = some 0) ↔ (val = 0)
      -- Use simp to handle the Decidable-dependent rewrite
      simp only [hEvalSrc, Option.some.injEq] at hiszero ⊢
      exact hiszero
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
      -- Extract Nat values from evalIRExpr for lhs
      have hlhsEval := eval_compileExpr_core_onExpr hL hexactL hbounded hpresentL hruntime
      rw [hlhs] at hlhsEval
      simp [Except.toOption] at hlhsEval
      rcases hLhsIR : evalIRExpr state lhsIR with _ | lhsVal
      · simp [hLhsIR, Option.bind] at hlhsEval
      · simp [hLhsIR, Option.bind] at hlhsEval
        have hLhsSrc : SourceSemantics.evalExpr fields runtime lhs = some lhsVal := hlhsEval.symm
        -- Extract Nat values from evalIRExpr for rhs
        have hrhsEval := eval_compileExpr_core_onExpr hR hexactR hbounded hpresentR hruntime
        rw [hrhs] at hrhsEval
        simp [Except.toOption] at hrhsEval
        rcases hRhsIR : evalIRExpr state rhsIR with _ | rhsVal
        · simp [hRhsIR, Option.bind] at hrhsEval
        · simp [hRhsIR, Option.bind] at hrhsEval
          have hRhsSrc : SourceSemantics.evalExpr fields runtime rhs = some rhsVal := hrhsEval.symm
          -- Boundedness
          have hlhsLt := evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime
          rw [hLhsSrc] at hlhsLt; simp at hlhsLt
          have hrhsLt := evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime
          rw [hRhsSrc] at hrhsLt; simp at hrhsLt
          refine ⟨YulExpr.call "lt" [lhsIR, rhsIR], ?_, ?_⟩
          · rw [CompilationModel.compileRequireFailCond, hlhs, hrhs]; rfl
          · have hltEval := evalIRExpr_lt_of_eval hLhsIR hRhsIR
            -- evalExpr (.ge lhs rhs) = do lhsV ← ...; rhsV ← ...; pure (boolWord (decide (rhsV ≤ lhsV)))
            -- With lhs = some lhsVal, rhs = some rhsVal:
            -- evalExpr (.ge lhs rhs) = some (boolWord (decide (rhsVal ≤ lhsVal)))
            -- evalExpr (.ge lhs rhs) = 0 means some (boolWord ...) = some 0 means boolWord ... = 0
            -- boolWord (decide (rhsVal ≤ lhsVal)) = 0 iff ¬ (rhsVal ≤ lhsVal) iff lhsVal < rhsVal
            -- So boolWord (evalExpr (.ge ...) = 0) = boolWord (lhsVal < rhsVal)
            --    = boolWord (lhsVal % evm < rhsVal % evm)  (since both < evmModulus)
            simp [Nat.mod_eq_of_lt hlhsLt, Nat.mod_eq_of_lt hrhsLt] at hltEval
            -- hltEval : evalIRExpr state (call "lt" [lhsIR, rhsIR]) = some (boolWord (lhsVal < rhsVal))
            -- Goal: evalIRExpr state (call "lt" [..]) = some (boolWord (decide (evalExpr (.ge ..) = some 0)))
            -- evalExpr (.ge lhs rhs) = some (boolWord (decide (rhsVal ≤ lhsVal)))
            have hGeEval : SourceSemantics.evalExpr fields runtime (.ge lhs rhs) =
                some (SourceSemantics.boolWord (decide (rhsVal ≤ lhsVal))) := by
              change (do let l ← SourceSemantics.evalExpr fields runtime lhs
                         let r ← SourceSemantics.evalExpr fields runtime rhs
                         pure (SourceSemantics.boolWord (decide (r ≤ l)))) = _
              rw [hLhsSrc, hRhsSrc]; rfl
            -- Reduce to: (lhsVal < rhsVal) ↔ ¬ (rhsVal ≤ lhsVal) ↔ (boolWord (decide (rhsVal ≤ lhsVal)) = 0)
            -- So boolWord (lhsVal < rhsVal) = boolWord (decide (some (boolWord ..) = some 0))
            -- Use simp only with hGeEval to handle the Decidable dependency
            rw [hltEval]
            simp only [Option.some.injEq, hGeEval, boolWord_eq_if]
            by_cases hle : rhsVal ≤ lhsVal
            · simp [hle, Nat.not_lt_of_le hle]
            · simp [hle, Nat.lt_of_not_le hle]
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
      -- Extract Nat values from evalIRExpr for lhs
      have hlhsEval := eval_compileExpr_core_onExpr hL hexactL hbounded hpresentL hruntime
      rw [hlhs] at hlhsEval
      simp [Except.toOption] at hlhsEval
      rcases hLhsIR : evalIRExpr state lhsIR with _ | lhsVal
      · simp [hLhsIR, Option.bind] at hlhsEval
      · simp [hLhsIR, Option.bind] at hlhsEval
        have hLhsSrc : SourceSemantics.evalExpr fields runtime lhs = some lhsVal := hlhsEval.symm
        -- Extract Nat values from evalIRExpr for rhs
        have hrhsEval := eval_compileExpr_core_onExpr hR hexactR hbounded hpresentR hruntime
        rw [hrhs] at hrhsEval
        simp [Except.toOption] at hrhsEval
        rcases hRhsIR : evalIRExpr state rhsIR with _ | rhsVal
        · simp [hRhsIR, Option.bind] at hrhsEval
        · simp [hRhsIR, Option.bind] at hrhsEval
          have hRhsSrc : SourceSemantics.evalExpr fields runtime rhs = some rhsVal := hrhsEval.symm
          -- Boundedness
          have hlhsLt := evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime
          rw [hLhsSrc] at hlhsLt; simp at hlhsLt
          have hrhsLt := evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime
          rw [hRhsSrc] at hrhsLt; simp at hrhsLt
          refine ⟨YulExpr.call "gt" [lhsIR, rhsIR], ?_, ?_⟩
          · rw [CompilationModel.compileRequireFailCond, hlhs, hrhs]; rfl
          · have hgtEval := evalIRExpr_gt_of_eval hLhsIR hRhsIR
            simp [Nat.mod_eq_of_lt hlhsLt, Nat.mod_eq_of_lt hrhsLt] at hgtEval
            -- hgtEval : evalIRExpr state (call "gt" [..]) = some (boolWord (rhsVal < lhsVal))
            have hLeEval : SourceSemantics.evalExpr fields runtime (.le lhs rhs) =
                some (SourceSemantics.boolWord (decide (lhsVal ≤ rhsVal))) := by
              change (do let l ← SourceSemantics.evalExpr fields runtime lhs
                         let r ← SourceSemantics.evalExpr fields runtime rhs
                         pure (SourceSemantics.boolWord (decide (l ≤ r)))) = _
              rw [hLhsSrc, hRhsSrc]; rfl
            rw [hgtEval]
            simp only [Option.some.injEq, hLeEval, boolWord_eq_if]
            by_cases hle : lhsVal ≤ rhsVal
            · simp [hle, Nat.not_lt_of_le hle]
            · simp [hle, Nat.lt_of_not_le hle]
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
  | bitAnd hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.bitAnd lhs rhs) from ExprCompileCore.bitAnd hL hR) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · simp [CompilationModel.compileRequireFailCond, hexpr]
      · simpa using finishIszeroEval (expr := .bitAnd lhs rhs)
          (show ExprCompileCore (.bitAnd lhs rhs) from ExprCompileCore.bitAnd hL hR) hexact hpresent hexpr
  | bitOr hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.bitOr lhs rhs) from ExprCompileCore.bitOr hL hR) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · simp [CompilationModel.compileRequireFailCond, hexpr]
      · simpa using finishIszeroEval (expr := .bitOr lhs rhs)
          (show ExprCompileCore (.bitOr lhs rhs) from ExprCompileCore.bitOr hL hR) hexact hpresent hexpr
  | bitXor hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.bitXor lhs rhs) from ExprCompileCore.bitXor hL hR) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · simp [CompilationModel.compileRequireFailCond, hexpr]
      · simpa using finishIszeroEval (expr := .bitXor lhs rhs)
          (show ExprCompileCore (.bitXor lhs rhs) from ExprCompileCore.bitXor hL hR) hexact hpresent hexpr
  | bitNot h =>
      rename_i expr
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.bitNot expr) from ExprCompileCore.bitNot h) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · simp [CompilationModel.compileRequireFailCond, hexpr]
      · simpa using finishIszeroEval (expr := .bitNot expr)
          (show ExprCompileCore (.bitNot expr) from ExprCompileCore.bitNot h) hexact hpresent hexpr
-- SORRY'D:   let finishIszeroEval {expr : Expr} (h : ExprCompileCore expr)
-- SORRY'D:       (hexactExpr : bindingsExactlyMatchIRVarsOnExpr expr runtime.bindings state)
-- SORRY'D:       (hpresentExpr : exprBoundNamesPresent expr runtime.bindings)
-- SORRY'D:       {exprIR : YulExpr}
-- SORRY'D:       (hexpr : CompilationModel.compileExpr fields .calldata expr = Except.ok exprIR) :
-- SORRY'D:       evalIRExpr state (YulExpr.call "iszero" [exprIR]) =
-- SORRY'D:         some (SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime expr = 0)) := by
-- SORRY'D:     have heval := eval_compileExpr_core_onExpr h hexactExpr hbounded hpresentExpr hruntime
-- SORRY'D:     rw [hexpr] at heval
-- SORRY'D:     have hlt := evalExpr_lt_evmModulus_core_onExpr h hexactExpr hbounded hpresentExpr hruntime
-- SORRY'D:     simpa [hexpr] using evalIRExpr_iszero_of_lt heval hlt
-- SORRY'D:   cases hcore with
-- SORRY'D:   | literal value =>
-- SORRY'D:       rcases compileExpr_core_ok (fields := fields)
-- SORRY'D:           (show ExprCompileCore (.literal value) from ExprCompileCore.literal value) with ⟨exprIR, hexpr⟩
-- SORRY'D:       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
-- SORRY'D:       · simp [CompilationModel.compileRequireFailCond, hexpr]
-- SORRY'D:       · simpa using finishIszeroEval (expr := .literal value)
-- SORRY'D:           (show ExprCompileCore (.literal value) from ExprCompileCore.literal value) hexact hpresent hexpr
-- SORRY'D:   | param name =>
-- SORRY'D:       rcases compileExpr_core_ok (fields := fields)
-- SORRY'D:           (show ExprCompileCore (.param name) from ExprCompileCore.param name) with ⟨exprIR, hexpr⟩
-- SORRY'D:       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
-- SORRY'D:       · simp [CompilationModel.compileRequireFailCond, hexpr]
-- SORRY'D:       · simpa using finishIszeroEval (expr := .param name)
-- SORRY'D:           (show ExprCompileCore (.param name) from ExprCompileCore.param name) hexact hpresent hexpr
-- SORRY'D:   | localVar name =>
-- SORRY'D:       rcases compileExpr_core_ok (fields := fields)
-- SORRY'D:           (show ExprCompileCore (.localVar name) from ExprCompileCore.localVar name) with ⟨exprIR, hexpr⟩
-- SORRY'D:       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
-- SORRY'D:       · simp [CompilationModel.compileRequireFailCond, hexpr]
-- SORRY'D:       · simpa using finishIszeroEval (expr := .localVar name)
-- SORRY'D:           (show ExprCompileCore (.localVar name) from ExprCompileCore.localVar name) hexact hpresent hexpr
-- SORRY'D:   | caller =>
-- SORRY'D:       rcases compileExpr_core_ok (fields := fields)
-- SORRY'D:           (show ExprCompileCore (.caller) from ExprCompileCore.caller) with ⟨exprIR, hexpr⟩
-- SORRY'D:       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
-- SORRY'D:       · simp [CompilationModel.compileRequireFailCond, hexpr]
-- SORRY'D:       · simpa using finishIszeroEval (expr := .caller)
-- SORRY'D:           (show ExprCompileCore (.caller) from ExprCompileCore.caller) hexact hpresent hexpr
-- SORRY'D:   | contractAddress =>
-- SORRY'D:       rcases compileExpr_core_ok (fields := fields)
-- SORRY'D:           (show ExprCompileCore (.contractAddress) from ExprCompileCore.contractAddress) with ⟨exprIR, hexpr⟩
-- SORRY'D:       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
-- SORRY'D:       · simp [CompilationModel.compileRequireFailCond, hexpr]
-- SORRY'D:       · simpa using finishIszeroEval (expr := .contractAddress)
-- SORRY'D:           (show ExprCompileCore (.contractAddress) from ExprCompileCore.contractAddress) hexact hpresent hexpr
-- SORRY'D:   | msgValue =>
-- SORRY'D:       rcases compileExpr_core_ok (fields := fields)
-- SORRY'D:           (show ExprCompileCore (.msgValue) from ExprCompileCore.msgValue) with ⟨exprIR, hexpr⟩
-- SORRY'D:       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
-- SORRY'D:       · simp [CompilationModel.compileRequireFailCond, hexpr]
-- SORRY'D:       · simpa using finishIszeroEval (expr := .msgValue)
-- SORRY'D:           (show ExprCompileCore (.msgValue) from ExprCompileCore.msgValue) hexact hpresent hexpr
-- SORRY'D:   | blockTimestamp =>
-- SORRY'D:       rcases compileExpr_core_ok (fields := fields)
-- SORRY'D:           (show ExprCompileCore (.blockTimestamp) from ExprCompileCore.blockTimestamp) with ⟨exprIR, hexpr⟩
-- SORRY'D:       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
-- SORRY'D:       · simp [CompilationModel.compileRequireFailCond, hexpr]
-- SORRY'D:       · simpa using finishIszeroEval (expr := .blockTimestamp)
-- SORRY'D:           (show ExprCompileCore (.blockTimestamp) from ExprCompileCore.blockTimestamp) hexact hpresent hexpr
-- SORRY'D:   | blockNumber =>
-- SORRY'D:       rcases compileExpr_core_ok (fields := fields)
-- SORRY'D:           (show ExprCompileCore (.blockNumber) from ExprCompileCore.blockNumber) with ⟨exprIR, hexpr⟩
-- SORRY'D:       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
-- SORRY'D:       · simp [CompilationModel.compileRequireFailCond, hexpr]
-- SORRY'D:       · simpa using finishIszeroEval (expr := .blockNumber)
-- SORRY'D:           (show ExprCompileCore (.blockNumber) from ExprCompileCore.blockNumber) hexact hpresent hexpr
-- SORRY'D:   | chainid =>
-- SORRY'D:       rcases compileExpr_core_ok (fields := fields)
-- SORRY'D:           (show ExprCompileCore (.chainid) from ExprCompileCore.chainid) with ⟨exprIR, hexpr⟩
-- SORRY'D:       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
-- SORRY'D:       · simp [CompilationModel.compileRequireFailCond, hexpr]
-- SORRY'D:       · simpa using finishIszeroEval (expr := .chainid)
-- SORRY'D:           (show ExprCompileCore (.chainid) from ExprCompileCore.chainid) hexact hpresent hexpr
-- SORRY'D:   | add hL hR =>
-- SORRY'D:       rename_i lhs rhs
-- SORRY'D:       rcases compileExpr_core_ok (fields := fields)
-- SORRY'D:           (show ExprCompileCore (.add lhs rhs) from ExprCompileCore.add hL hR) with ⟨exprIR, hexpr⟩
-- SORRY'D:       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
-- SORRY'D:       · simp [CompilationModel.compileRequireFailCond, hexpr]
-- SORRY'D:       · simpa using finishIszeroEval (expr := .add lhs rhs)
-- SORRY'D:           (show ExprCompileCore (.add lhs rhs) from ExprCompileCore.add hL hR) hexact hpresent hexpr
-- SORRY'D:   | sub hL hR =>
-- SORRY'D:       rename_i lhs rhs
-- SORRY'D:       rcases compileExpr_core_ok (fields := fields)
-- SORRY'D:           (show ExprCompileCore (.sub lhs rhs) from ExprCompileCore.sub hL hR) with ⟨exprIR, hexpr⟩
-- SORRY'D:       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
-- SORRY'D:       · simp [CompilationModel.compileRequireFailCond, hexpr]
-- SORRY'D:       · simpa using finishIszeroEval (expr := .sub lhs rhs)
-- SORRY'D:           (show ExprCompileCore (.sub lhs rhs) from ExprCompileCore.sub hL hR) hexact hpresent hexpr
-- SORRY'D:   | mul hL hR =>
-- SORRY'D:       rename_i lhs rhs
-- SORRY'D:       rcases compileExpr_core_ok (fields := fields)
-- SORRY'D:           (show ExprCompileCore (.mul lhs rhs) from ExprCompileCore.mul hL hR) with ⟨exprIR, hexpr⟩
-- SORRY'D:       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
-- SORRY'D:       · simp [CompilationModel.compileRequireFailCond, hexpr]
-- SORRY'D:       · simpa using finishIszeroEval (expr := .mul lhs rhs)
-- SORRY'D:           (show ExprCompileCore (.mul lhs rhs) from ExprCompileCore.mul hL hR) hexact hpresent hexpr
-- SORRY'D:   | div hL hR =>
-- SORRY'D:       rename_i lhs rhs
-- SORRY'D:       rcases compileExpr_core_ok (fields := fields)
-- SORRY'D:           (show ExprCompileCore (.div lhs rhs) from ExprCompileCore.div hL hR) with ⟨exprIR, hexpr⟩
-- SORRY'D:       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
-- SORRY'D:       · simp [CompilationModel.compileRequireFailCond, hexpr]
-- SORRY'D:       · simpa using finishIszeroEval (expr := .div lhs rhs)
-- SORRY'D:           (show ExprCompileCore (.div lhs rhs) from ExprCompileCore.div hL hR) hexact hpresent hexpr
-- SORRY'D:   | mod hL hR =>
-- SORRY'D:       rename_i lhs rhs
-- SORRY'D:       rcases compileExpr_core_ok (fields := fields)
-- SORRY'D:           (show ExprCompileCore (.mod lhs rhs) from ExprCompileCore.mod hL hR) with ⟨exprIR, hexpr⟩
-- SORRY'D:       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
-- SORRY'D:       · simp [CompilationModel.compileRequireFailCond, hexpr]
-- SORRY'D:       · simpa using finishIszeroEval (expr := .mod lhs rhs)
-- SORRY'D:           (show ExprCompileCore (.mod lhs rhs) from ExprCompileCore.mod hL hR) hexact hpresent hexpr
-- SORRY'D:   | eq hL hR =>
-- SORRY'D:       rename_i lhs rhs
-- SORRY'D:       rcases compileExpr_core_ok (fields := fields)
-- SORRY'D:           (show ExprCompileCore (.eq lhs rhs) from ExprCompileCore.eq hL hR) with ⟨exprIR, hexpr⟩
-- SORRY'D:       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
-- SORRY'D:       · simp [CompilationModel.compileRequireFailCond, hexpr]
-- SORRY'D:       · simpa using finishIszeroEval (expr := .eq lhs rhs)
-- SORRY'D:           (show ExprCompileCore (.eq lhs rhs) from ExprCompileCore.eq hL hR) hexact hpresent hexpr
-- SORRY'D:   | lt hL hR =>
-- SORRY'D:       rename_i lhs rhs
-- SORRY'D:       rcases compileExpr_core_ok (fields := fields)
-- SORRY'D:           (show ExprCompileCore (.lt lhs rhs) from ExprCompileCore.lt hL hR) with ⟨exprIR, hexpr⟩
-- SORRY'D:       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
-- SORRY'D:       · simp [CompilationModel.compileRequireFailCond, hexpr]
-- SORRY'D:       · simpa using finishIszeroEval (expr := .lt lhs rhs)
-- SORRY'D:           (show ExprCompileCore (.lt lhs rhs) from ExprCompileCore.lt hL hR) hexact hpresent hexpr
-- SORRY'D:   | gt hL hR =>
-- SORRY'D:       rename_i lhs rhs
-- SORRY'D:       rcases compileExpr_core_ok (fields := fields)
-- SORRY'D:           (show ExprCompileCore (.gt lhs rhs) from ExprCompileCore.gt hL hR) with ⟨exprIR, hexpr⟩
-- SORRY'D:       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
-- SORRY'D:       · simp [CompilationModel.compileRequireFailCond, hexpr]
-- SORRY'D:       · simpa using finishIszeroEval (expr := .gt lhs rhs)
-- SORRY'D:           (show ExprCompileCore (.gt lhs rhs) from ExprCompileCore.gt hL hR) hexact hpresent hexpr
-- SORRY'D:   | ge hL hR =>
-- SORRY'D:       rename_i lhs rhs
-- SORRY'D:       rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
-- SORRY'D:       rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
-- SORRY'D:       have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
-- SORRY'D:         bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
-- SORRY'D:           intro name hname
-- SORRY'D:           simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hname))
-- SORRY'D:       have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
-- SORRY'D:         bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
-- SORRY'D:           intro name hname
-- SORRY'D:           simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hname))
-- SORRY'D:       have hpresentL : exprBoundNamesPresent lhs runtime.bindings :=
-- SORRY'D:         exprBoundNamesPresent_of_subset hpresent (by
-- SORRY'D:           intro name hname
-- SORRY'D:           simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hname))
-- SORRY'D:       have hpresentR : exprBoundNamesPresent rhs runtime.bindings :=
-- SORRY'D:         exprBoundNamesPresent_of_subset hpresent (by
-- SORRY'D:           intro name hname
-- SORRY'D:           simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hname))
-- SORRY'D:       have hlhsEval := eval_compileExpr_core_onExpr hL hexactL hbounded hpresentL hruntime
-- SORRY'D:       have hrhsEval := eval_compileExpr_core_onExpr hR hexactR hbounded hpresentR hruntime
-- SORRY'D:       rw [hlhs] at hlhsEval
-- SORRY'D:       rw [hrhs] at hrhsEval
-- SORRY'D:       have hlhsLt := evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime
-- SORRY'D:       have hrhsLt := evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime
-- SORRY'D:       refine ⟨YulExpr.call "lt" [lhsIR, rhsIR], ?_, ?_⟩
-- SORRY'D:       · rw [CompilationModel.compileRequireFailCond, hlhs, hrhs]
-- SORRY'D:         rfl
-- SORRY'D:       · have hltEval :
-- SORRY'D:             evalIRExpr state (YulExpr.call "lt" [lhsIR, rhsIR]) =
-- SORRY'D:               some (SourceSemantics.boolWord
-- SORRY'D:                 (SourceSemantics.evalExpr fields runtime lhs % Compiler.Constants.evmModulus <
-- SORRY'D:                   SourceSemantics.evalExpr fields runtime rhs % Compiler.Constants.evmModulus)) := by
-- SORRY'D:           simpa using evalIRExpr_lt_of_eval hlhsEval hrhsEval
-- SORRY'D:         rw [show SourceSemantics.evalExpr fields runtime (.ge lhs rhs) =
-- SORRY'D:             SourceSemantics.boolWord (decide (SourceSemantics.evalExpr fields runtime rhs ≤
-- SORRY'D:               SourceSemantics.evalExpr fields runtime lhs)) by rfl]
-- SORRY'D:         by_cases hlt : SourceSemantics.evalExpr fields runtime lhs < SourceSemantics.evalExpr fields runtime rhs
-- SORRY'D:         · have hnotge : ¬ (SourceSemantics.evalExpr fields runtime rhs ≤
-- SORRY'D:             SourceSemantics.evalExpr fields runtime lhs) := Nat.not_le_of_gt hlt
-- SORRY'D:           simp [hltEval, Nat.mod_eq_of_lt hlhsLt, Nat.mod_eq_of_lt hrhsLt, hlt, hnotge,
-- SORRY'D:             SourceSemantics.boolWord]
-- SORRY'D:         · have hge : SourceSemantics.evalExpr fields runtime rhs ≤
-- SORRY'D:             SourceSemantics.evalExpr fields runtime lhs := Nat.le_of_not_gt hlt
-- SORRY'D:           simp [hltEval, Nat.mod_eq_of_lt hlhsLt, Nat.mod_eq_of_lt hrhsLt, hlt, hge,
-- SORRY'D:             SourceSemantics.boolWord]
-- SORRY'D:   | le hL hR =>
-- SORRY'D:       rename_i lhs rhs
-- SORRY'D:       rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
-- SORRY'D:       rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
-- SORRY'D:       have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
-- SORRY'D:         bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
-- SORRY'D:           intro name hname
-- SORRY'D:           simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hname))
-- SORRY'D:       have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
-- SORRY'D:         bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
-- SORRY'D:           intro name hname
-- SORRY'D:           simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hname))
-- SORRY'D:       have hpresentL : exprBoundNamesPresent lhs runtime.bindings :=
-- SORRY'D:         exprBoundNamesPresent_of_subset hpresent (by
-- SORRY'D:           intro name hname
-- SORRY'D:           simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hname))
-- SORRY'D:       have hpresentR : exprBoundNamesPresent rhs runtime.bindings :=
-- SORRY'D:         exprBoundNamesPresent_of_subset hpresent (by
-- SORRY'D:           intro name hname
-- SORRY'D:           simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hname))
-- SORRY'D:       have hlhsEval := eval_compileExpr_core_onExpr hL hexactL hbounded hpresentL hruntime
-- SORRY'D:       have hrhsEval := eval_compileExpr_core_onExpr hR hexactR hbounded hpresentR hruntime
-- SORRY'D:       rw [hlhs] at hlhsEval
-- SORRY'D:       rw [hrhs] at hrhsEval
-- SORRY'D:       have hlhsLt := evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime
-- SORRY'D:       have hrhsLt := evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime
-- SORRY'D:       refine ⟨YulExpr.call "gt" [lhsIR, rhsIR], ?_, ?_⟩
-- SORRY'D:       · rw [CompilationModel.compileRequireFailCond, hlhs, hrhs]
-- SORRY'D:         rfl
-- SORRY'D:       · have hgtEval :
-- SORRY'D:             evalIRExpr state (YulExpr.call "gt" [lhsIR, rhsIR]) =
-- SORRY'D:               some (SourceSemantics.boolWord
-- SORRY'D:                 (SourceSemantics.evalExpr fields runtime rhs % Compiler.Constants.evmModulus <
-- SORRY'D:                   SourceSemantics.evalExpr fields runtime lhs % Compiler.Constants.evmModulus)) := by
-- SORRY'D:           simpa using evalIRExpr_gt_of_eval hlhsEval hrhsEval
-- SORRY'D:         rw [show SourceSemantics.evalExpr fields runtime (.le lhs rhs) =
-- SORRY'D:             SourceSemantics.boolWord (decide (SourceSemantics.evalExpr fields runtime lhs ≤
-- SORRY'D:               SourceSemantics.evalExpr fields runtime rhs)) by rfl]
-- SORRY'D:         by_cases hgt : SourceSemantics.evalExpr fields runtime rhs < SourceSemantics.evalExpr fields runtime lhs
-- SORRY'D:         · have hnotle : ¬ (SourceSemantics.evalExpr fields runtime lhs ≤
-- SORRY'D:             SourceSemantics.evalExpr fields runtime rhs) := Nat.not_le_of_gt hgt
-- SORRY'D:           simp [hgtEval, Nat.mod_eq_of_lt hlhsLt, Nat.mod_eq_of_lt hrhsLt, hgt, hnotle,
-- SORRY'D:             SourceSemantics.boolWord]
-- SORRY'D:         · have hle : SourceSemantics.evalExpr fields runtime lhs ≤
-- SORRY'D:             SourceSemantics.evalExpr fields runtime rhs := Nat.le_of_not_gt hgt
-- SORRY'D:           simp [hgtEval, Nat.mod_eq_of_lt hlhsLt, Nat.mod_eq_of_lt hrhsLt, hgt, hle,
-- SORRY'D:             SourceSemantics.boolWord]
-- SORRY'D:   | logicalNot h =>
-- SORRY'D:       rename_i expr
-- SORRY'D:       rcases compileExpr_core_ok (fields := fields)
-- SORRY'D:           (show ExprCompileCore (.logicalNot expr) from ExprCompileCore.logicalNot h) with ⟨exprIR, hexpr⟩
-- SORRY'D:       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
-- SORRY'D:       · simp [CompilationModel.compileRequireFailCond, hexpr]
-- SORRY'D:       · simpa using finishIszeroEval (expr := .logicalNot expr)
-- SORRY'D:           (show ExprCompileCore (.logicalNot expr) from ExprCompileCore.logicalNot h) hexact hpresent hexpr
-- SORRY'D:   | logicalAnd hL hR =>
-- SORRY'D:       rename_i lhs rhs
-- SORRY'D:       rcases compileExpr_core_ok (fields := fields)
-- SORRY'D:           (show ExprCompileCore (.logicalAnd lhs rhs) from ExprCompileCore.logicalAnd hL hR) with ⟨exprIR, hexpr⟩
-- SORRY'D:       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
-- SORRY'D:       · simp [CompilationModel.compileRequireFailCond, hexpr]
-- SORRY'D:       · simpa using finishIszeroEval (expr := .logicalAnd lhs rhs)
-- SORRY'D:           (show ExprCompileCore (.logicalAnd lhs rhs) from ExprCompileCore.logicalAnd hL hR) hexact hpresent hexpr
-- SORRY'D:   | logicalOr hL hR =>
-- SORRY'D:       rename_i lhs rhs
-- SORRY'D:       rcases compileExpr_core_ok (fields := fields)
-- SORRY'D:           (show ExprCompileCore (.logicalOr lhs rhs) from ExprCompileCore.logicalOr hL hR) with ⟨exprIR, hexpr⟩
-- SORRY'D:       refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
-- SORRY'D:       · simp [CompilationModel.compileRequireFailCond, hexpr]
-- SORRY'D:       · simpa using finishIszeroEval (expr := .logicalOr lhs rhs)
-- SORRY'D:           (show ExprCompileCore (.logicalOr lhs rhs) from ExprCompileCore.logicalOr hL hR) hexact hpresent hexpr

-- TYPESIG_SORRY: theorem eval_compileRequireFailCond_core
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {runtime : SourceSemantics.RuntimeState}
-- TYPESIG_SORRY:     {state : IRState}
-- TYPESIG_SORRY:     {cond : Expr}
-- TYPESIG_SORRY:     (hcore : ExprCompileCore cond)
-- TYPESIG_SORRY:     (hexact : bindingsExactlyMatchIRVars runtime.bindings state)
-- TYPESIG_SORRY:     (hbounded : bindingsBounded runtime.bindings)
-- TYPESIG_SORRY:     (hpresent : exprBoundNamesPresent cond runtime.bindings)
-- TYPESIG_SORRY:     (hruntime : runtimeStateMatchesIR fields runtime state) :
-- TYPESIG_SORRY:     ∃ failCond,
-- TYPESIG_SORRY:       CompilationModel.compileRequireFailCond fields .calldata cond = Except.ok failCond ∧
-- TYPESIG_SORRY:       evalIRExpr state failCond =
-- TYPESIG_SORRY:         some (SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime cond = 0)) := by sorry

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
    (offset : Nat) (value : Nat)
    (hvalue : value < Verity.Core.Uint256.modulus) :
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
  simp only [runtimeStateMatchesIR] at hmatch ⊢
  obtain ⟨hstor, htrans, hsender, hmsgVal, hthis, hts, hbn, hcid, hret, hevt⟩ := hmatch
  refine ⟨?_, ?_, hsender, hmsgVal, hthis, hts, hbn, hcid, hret, hevt⟩
  · -- storage: encodeStorageAt doesn't depend on transientStorage
    rw [hstor]
    funext slot
    exact SourceSemantics.encodeStorageAt_congr rfl rfl rfl
  · -- transientStorage
    funext o
    by_cases ho : o = offset
    · subst ho
      simp only [ite_true, Verity.Core.Uint256.ofNat, Nat.mod_eq_of_lt hvalue]
    · simp [ho]
      exact congrFun htrans o

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
  simpa using SourceSemantics.encodeStorage_withTransactionContext spec world tx

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

/-- Helper: `eval_compileExpr_core` implies both `evalIRExpr` and source `evalExpr`
succeed with the same `Nat` value. This factored lemma avoids repeating the
monadic-bind unfold in every statement proof. -/
theorem eval_compileExpr_core_split
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {expr : Expr}
    {exprIR : YulExpr}
    (hcore : ExprCompileCore expr)
    (hexact : bindingsExactlyMatchIRVars runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hpresent : exprBoundNamesPresent expr runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state)
    (hcompile : CompilationModel.compileExpr fields .calldata expr = Except.ok exprIR) :
    ∃ v, evalIRExpr state exprIR = some v ∧
         SourceSemantics.evalExpr fields runtime expr = some v ∧
         v < Compiler.Constants.evmModulus := by
  have heval := eval_compileExpr_core hcore hexact hbounded hpresent hruntime
  rw [hcompile] at heval
  simp [Except.toOption] at heval
  rcases hIR : evalIRExpr state exprIR with _ | v
  · simp [hIR, Option.bind] at heval
  · refine ⟨v, rfl, ?_, ?_⟩
    · simp [hIR, Option.bind] at heval
      exact heval.symm
    · have hlt := evalExpr_lt_evmModulus_core hcore hexact hbounded hpresent hruntime
      simp [hIR, Option.bind] at heval
      rw [heval.symm] at hlt
      -- hlt : some v < evmModulus, which Lean elaborates as v < evmModulus
      exact hlt

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
  · rw [CompilationModel.compileStmt, hvalueIR]; rfl
  · -- Get the bridge: both evaluations succeed with same value
    have heval := eval_compileExpr_core hcore hexact hbounded hpresent hruntime
    rw [hvalueIR] at heval
    simp [Except.toOption] at heval
    -- heval now relates evalIRExpr and evalExpr via Option bind
    -- Source: execStmt letVar does match evalExpr ... with some v => continue | none => revert
    -- IR: execIRStmts on [let_ name valueIR] does match evalIRExpr state valueIR with some v => continue (setVar) | none => revert
    simp only [SourceSemantics.execStmt, execIRStmts, List.length, execIRStmt]
    -- Now we need to case-split on evalIRExpr state valueIR
    rcases hIR : evalIRExpr state valueIR with _ | v
    · -- evalIRExpr returns none → but eval_compileExpr_core says it returns some
      simp [hIR, Option.bind] at heval
    · -- evalIRExpr returns some v
      simp [hIR, Option.bind] at heval
      -- heval : some v = evalExpr fields runtime value (up to wrapping)
      -- Now source side: evalExpr returns some v too
      rw [show SourceSemantics.evalExpr fields runtime value = some v from heval.symm]
      simp [stmtResultMatchesIRExec, stmtResultMatchesIRExecExact]
      have hlt := evalExpr_lt_evmModulus_core hcore hexact hbounded hpresent hruntime
      rw [heval.symm] at hlt
      exact ⟨hruntime, bindingsExactlyMatchIRVars_setVar_bindValue hexact name v,
             bindingsBounded_bindValue hbounded name v hlt⟩

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
  · rw [CompilationModel.compileStmt, hvalueIR]; rfl
  · have heval := eval_compileExpr_core hcore hexact hbounded hpresent hruntime
    rw [hvalueIR] at heval
    simp [Except.toOption] at heval
    simp only [SourceSemantics.execStmt, execIRStmts, List.length, execIRStmt]
    rcases hIR : evalIRExpr state valueIR with _ | v
    · simp [hIR, Option.bind] at heval
    · simp [hIR, Option.bind] at heval
      rw [show SourceSemantics.evalExpr fields runtime value = some v from heval.symm]
      simp [stmtResultMatchesIRExec, stmtResultMatchesIRExecExact]
      have hlt := evalExpr_lt_evmModulus_core hcore hexact hbounded hpresent hruntime
      rw [heval.symm] at hlt
      exact ⟨hruntime, bindingsExactlyMatchIRVars_setVar_bindValue hexact name v,
             bindingsBounded_bindValue hbounded name v hlt⟩

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
  refine ⟨[ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
          , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ], ?_, ?_⟩
  · rw [CompilationModel.compileStmt, hvalueIR]; rfl
  · have heval := eval_compileExpr_core hcore hexact hbounded hpresent hruntime
    rw [hvalueIR] at heval
    simp [Except.toOption] at heval
    simp only [SourceSemantics.execStmt, execIRStmts, List.length, execIRStmt, evalIRExpr,
               evalIRExprs]
    rcases hIR : evalIRExpr state valueIR with _ | v
    · simp [hIR, Option.bind] at heval
    · simp [hIR, Option.bind] at heval
      rw [show SourceSemantics.evalExpr fields runtime value = some v from heval.symm]
      simp [stmtResultMatchesIRExec, stmtResultMatchesIRExecExact]
      exact ⟨hruntime, hexact, hbounded⟩

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
  refine ⟨[ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
          , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ], ?_, ?_⟩
  · rw [CompilationModel.compileStmt, hvalueIR]; rfl
  · have heval := eval_compileExpr_core hcore hexact hbounded hpresent hruntime
    rw [hvalueIR] at heval
    simp [Except.toOption] at heval
    simp only [SourceSemantics.execStmt]
    rcases hIR : evalIRExpr state valueIR with _ | v
    · simp [hIR, Option.bind] at heval
    · simp [hIR, Option.bind] at heval
      rw [show SourceSemantics.evalExpr fields runtime value = some v from heval.symm]
      -- Reduce source side
      simp only [SourceSemantics.execStmt, List.length]
      -- Compute the IR execution result
      have hexec : execIRStmts (2 + extraFuel + 1) state
          [ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
          , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] =
          .return v { state with memory := fun o => if o = 0 then v else state.memory o } := by
        have : 2 + extraFuel + 1 = Nat.succ (Nat.succ (Nat.succ extraFuel)) := by omega
        rw [this]
        -- Now simp can unfold because fuel is Nat.succ form
        simp only [execIRStmts, execIRStmt, evalIRExpr, evalIRExprs, hIR, Option.bind,
                   ite_true, ite_false]
      -- Rewrite the goal to use the computed result
      show stmtResultMatchesIRExec fields (.return v runtime) _ ∧
           stmtResultMatchesIRExecExact (.return v runtime) _
      rw [hexec]
      exact ⟨⟨rfl, hruntime⟩, hexact, hbounded⟩

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
        some (SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime cond = some 0)) :=
  eval_compileRequireFailCond_core_onExpr hcore
    (bindingsExactlyMatchIRVarsOnScope_implies_onExpr hexact hinScope)
    hbounded hpresent hruntime

-- TYPESIG_SORRY: theorem eval_compileRequireFailCond_core_of_scope
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {runtime : SourceSemantics.RuntimeState}
-- TYPESIG_SORRY:     {state : IRState}
-- TYPESIG_SORRY:     {scope : List String}
-- TYPESIG_SORRY:     {cond : Expr}
-- TYPESIG_SORRY:     (hcore : ExprCompileCore cond)
-- TYPESIG_SORRY:     (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
-- TYPESIG_SORRY:     (hinScope : exprBoundNamesInScope cond scope)
-- TYPESIG_SORRY:     (hbounded : bindingsBounded runtime.bindings)
-- TYPESIG_SORRY:     (hpresent : exprBoundNamesPresent cond runtime.bindings)
-- TYPESIG_SORRY:     (hruntime : runtimeStateMatchesIR fields runtime state) :
-- TYPESIG_SORRY:     ∃ failCond,
-- TYPESIG_SORRY:       CompilationModel.compileRequireFailCond fields .calldata cond = Except.ok failCond ∧
-- TYPESIG_SORRY:       evalIRExpr state failCond =
-- TYPESIG_SORRY:         some (SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime cond = 0)) := by sorry

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

/-! ### Scope-independence of compileStmt / compileStmtList success

`compileStmt` uses `inScopeNames` only in `ite` (for `pickFreshName` + recursive
`compileStmtList` on branches) and `forEach` (for recursive `compileStmtList` on body).
Since `pickFreshName` is total and `compileExpr` / all other helpers ignore `inScopeNames`,
compilation success is scope-independent: if it succeeds with one scope, it succeeds
with any other. -/

private theorem compileStmt_ok_any_scope_aux
    (n : Nat)
    (fields : List Field) :
    (∀ (stmt : Stmt) (scope1 scope2 : List String),
      sizeOf stmt < n →
      (∃ ir, CompilationModel.compileStmt fields [] [] .calldata [] false scope1 stmt =
        Except.ok ir) →
      ∃ ir', CompilationModel.compileStmt fields [] [] .calldata [] false scope2 stmt =
        Except.ok ir') ∧
    (∀ (stmts : List Stmt) (scope1 scope2 : List String),
      sizeOf stmts < n →
      (∃ ir, CompilationModel.compileStmtList fields [] [] .calldata [] false scope1 stmts =
        Except.ok ir) →
      ∃ ir', CompilationModel.compileStmtList fields [] [] .calldata [] false scope2 stmts =
        Except.ok ir') := by
  induction n with
  | zero => exact ⟨fun _ _ _ h => absurd h (Nat.not_lt_zero _),
                    fun _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ n ih =>
    constructor
    · -- compileStmt part
      intro stmt scope1 scope2 hlt hok
      cases stmt with
      | ite cond thenBranch elseBranch =>
          rcases hok with ⟨ir, hir⟩
          simp only [CompilationModel.compileStmt, bind, Except.bind] at hir ⊢
          cases hcond : CompilationModel.compileExpr fields .calldata cond with
          | error e => simp [hcond] at hir
          | ok condIR =>
            simp only [hcond] at hir ⊢
            cases hthen1 : CompilationModel.compileStmtList
                fields [] [] .calldata [] false scope1 thenBranch with
            | error e => simp [hthen1] at hir
            | ok thenIR1 =>
              simp only [hthen1] at hir
              cases helse1 : CompilationModel.compileStmtList
                  fields [] [] .calldata [] false scope1 elseBranch with
              | error e => simp [helse1] at hir
              | ok elseIR1 =>
                rcases ih.2 thenBranch scope1 scope2
                    (by simp [Stmt.ite.sizeOf_spec] at hlt; omega) ⟨thenIR1, hthen1⟩
                  with ⟨thenIR2, hthen2⟩
                rcases ih.2 elseBranch scope1 scope2
                    (by simp [Stmt.ite.sizeOf_spec] at hlt; omega) ⟨elseIR1, helse1⟩
                  with ⟨elseIR2, helse2⟩
                simp only [hthen2, helse2]
                cases elseBranch.isEmpty <;> exact ⟨_, rfl⟩
      | forEach varName count body =>
          rcases hok with ⟨ir, hir⟩
          simp only [CompilationModel.compileStmt, bind, Except.bind] at hir ⊢
          cases hcount : CompilationModel.compileExpr fields .calldata count with
          | error e => simp [hcount] at hir
          | ok countIR =>
            simp only [hcount] at hir ⊢
            cases hbody1 : CompilationModel.compileStmtList
                fields [] [] .calldata [] false (varName :: scope1) body with
            | error e => simp [hbody1] at hir
            | ok bodyIR1 =>
              rcases ih.2 body (varName :: scope1) (varName :: scope2)
                  (by simp [Stmt.forEach.sizeOf_spec] at hlt; omega) ⟨bodyIR1, hbody1⟩
                with ⟨bodyIR2, hbody2⟩
              simp only [hbody2]
              exact ⟨_, rfl⟩
      -- All remaining cases: inScopeNames is unused, so the result is identical
      | letVar | assignVar | setStorage | setStorageAddr | storageArrayPush
      | storageArrayPop | setStorageArrayElement | setMapping | setMappingWord
      | setMappingPackedWord | setMapping2 | setMapping2Word | setMappingUint
      | setMappingChain | setStructMember | setStructMember2 | require
      | requireError | revertError | «return» | returnValues | returnArray
      | returnBytes | returnStorageWords | mstore | tstore | calldatacopy
      | returndataCopy | revertReturndata | stop | emit | internalCall
      | internalCallAssign | externalCallBind | ecm | rawLog =>
          simp only [CompilationModel.compileStmt] at hok ⊢; exact hok
    · -- compileStmtList part
      intro stmts scope1 scope2 hlt hok
      cases stmts with
      | nil => exact ⟨[], rfl⟩
      | cons s ss =>
          rcases hok with ⟨ir, hir⟩
          simp only [CompilationModel.compileStmtList, bind, Except.bind] at hir ⊢
          cases hs1 : CompilationModel.compileStmt
              fields [] [] .calldata [] false scope1 s with
          | error e => simp [hs1] at hir
          | ok headIR1 =>
            simp only [hs1] at hir
            cases hss1 : CompilationModel.compileStmtList
                fields [] [] .calldata [] false (collectStmtNames s ++ scope1) ss with
            | error e => simp [hss1] at hir
            | ok tailIR1 =>
              rcases ih.1 s scope1 scope2 (by simp [List.cons.sizeOf_spec] at hlt; omega)
                  ⟨headIR1, hs1⟩ with ⟨headIR2, hs2⟩
              rcases ih.2 ss (collectStmtNames s ++ scope1) (collectStmtNames s ++ scope2)
                  (by simp [List.cons.sizeOf_spec] at hlt; omega) ⟨tailIR1, hss1⟩
                with ⟨tailIR2, hss2⟩
              simp only [hs2, hss2]
              exact ⟨_, rfl⟩

theorem compileStmt_ok_any_scope
    {fields : List Field}
    {scope1 scope2 : List String}
    {stmt : Stmt}
    (hok : ∃ ir, CompilationModel.compileStmt
      fields [] [] .calldata [] false scope1 stmt = Except.ok ir) :
    ∃ ir', CompilationModel.compileStmt
      fields [] [] .calldata [] false scope2 stmt = Except.ok ir' :=
  (compileStmt_ok_any_scope_aux (sizeOf stmt + 1) fields).1 stmt scope1 scope2
    (Nat.lt_succ_of_le (Nat.le_refl _)) hok

theorem compileStmtList_ok_any_scope
    {fields : List Field}
    {scope1 scope2 : List String}
    {stmts : List Stmt}
    (hok : ∃ ir, CompilationModel.compileStmtList
      fields [] [] .calldata [] false scope1 stmts = Except.ok ir) :
    ∃ ir', CompilationModel.compileStmtList
      fields [] [] .calldata [] false scope2 stmts = Except.ok ir' :=
  (compileStmt_ok_any_scope_aux (sizeOf stmts + 1) fields).2 stmts scope1 scope2
    (Nat.lt_succ_of_le (Nat.le_refl _)) hok

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

theorem execIRStmts_revertWithMessage_revert
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
      -- Get the eval_compileExpr_core result (elaborated via monadic binding)
      have heval := eval_compileExpr_core hvalue hexact hbounded hpresent hruntime
      rw [hvalueIR] at heval; simp [Except.toOption] at heval
      -- Extract the Nat value from the IR evaluation
      rcases hIR : evalIRExpr state valueIR with _ | valueNat
      · -- evalIRExpr = none: contradicts eval_compileExpr_core
        simp [hIR, Option.bind] at heval
      · -- evalIRExpr = some valueNat
        simp [hIR, Option.bind] at heval
        -- heval : some valueNat = evalExpr fields runtime value, so evalExpr = some valueNat
        have hEvalSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
          heval.symm
        let runtime' :=
          { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
        let state' := state.setVar name valueNat
        have hvalueLt := evalExpr_lt_evmModulus_core hvalue hexact hbounded hpresent hruntime
        rw [hEvalSrc] at hvalueLt; simp at hvalueLt
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
            simp [execIRStmt, hIR, state']
          have hirExec :
              execIRStmts (tailIR.length + 2) state
                (YulStmt.let_ name valueIR :: tailIR) =
                execIRStmts (tailIR.length + 1) state' tailIR := by
            simpa using
              (execIRStmts_cons_of_execIRStmt_continue state state'
                (YulStmt.let_ name valueIR) tailIR hstmt)
          rw [SourceSemantics.execStmtList, SourceSemantics.execStmt, hEvalSrc]
          dsimp [runtime', state']
          constructor
          · simpa [hirExec, runtime'] using htailSem
          · simpa [hirExec, runtime'] using htailExact
  | assignVar hvalue hinScope hrest ih =>
      rename_i scope name value rest
      have hpresent : exprBoundNamesPresent value runtime.bindings :=
        exprBoundNamesPresent_of_scope hscope hinScope
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      have heval := eval_compileExpr_core hvalue hexact hbounded hpresent hruntime
      rw [hvalueIR] at heval; simp [Except.toOption] at heval
      rcases hIR : evalIRExpr state valueIR with _ | valueNat
      · simp [hIR, Option.bind] at heval
      · simp [hIR, Option.bind] at heval
        have hEvalSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
          heval.symm
        let runtime' :=
          { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
        let state' := state.setVar name valueNat
        have hvalueLt := evalExpr_lt_evmModulus_core hvalue hexact hbounded hpresent hruntime
        rw [hEvalSrc] at hvalueLt; simp at hvalueLt
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
            simp [execIRStmt, hIR, state']
          have hirExec :
              execIRStmts (tailIR.length + 2) state
                (YulStmt.assign name valueIR :: tailIR) =
                execIRStmts (tailIR.length + 1) state' tailIR := by
            simpa using
              (execIRStmts_cons_of_execIRStmt_continue state state'
                (YulStmt.assign name valueIR) tailIR hstmt)
          rw [SourceSemantics.execStmtList, SourceSemantics.execStmt, hEvalSrc]
          dsimp [runtime', state']
          constructor
          · simpa [hirExec, runtime'] using htailSem
          · simpa [hirExec, runtime'] using htailExact
  | require_ hcond hinScope hrest ih =>
      rename_i scope cond message rest
      have hpresent : exprBoundNamesPresent cond runtime.bindings :=
        exprBoundNamesPresent_of_scope hscope hinScope
      -- First, establish that evalExpr cond is some, using eval_compileExpr_core
      rcases compileExpr_core_ok hcond with ⟨condIR, hcondIR⟩
      have hCondEval := eval_compileExpr_core hcond hexact hbounded hpresent hruntime
      rw [hcondIR] at hCondEval; simp [Except.toOption] at hCondEval
      rcases hCondIRVal : evalIRExpr state condIR with _ | condVal
      · simp [hCondIRVal, Option.bind] at hCondEval
      · simp [hCondIRVal, Option.bind] at hCondEval
        have hCondSrc : SourceSemantics.evalExpr fields runtime cond = some condVal :=
          hCondEval.symm
        -- Get the fail condition IR
        rcases eval_compileRequireFailCond_core_onExpr hcond
            (bindingsExactlyMatchIRVars_implies_onExpr hexact)
            hbounded hpresent hruntime with
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
        · rw [SourceSemantics.execStmtList, SourceSemantics.execStmt, hCondSrc]
          by_cases hzero : condVal = 0
          · -- condVal = 0 → require fails → revert
            rcases execIRStmts_revertWithMessage_revert (fuel := tailIR.length) (state := state) message with
              ⟨revState, hrev⟩
            have hfailEval' : evalIRExpr state failCond = some 1 := by
              rw [hCondSrc, hzero] at hfailEval
              simpa [SourceSemantics.boolWord] using hfailEval
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
            simp [hzero, hirExec, stmtResultMatchesIRExec, stmtResultMatchesIRExecExact]
          · -- condVal ≠ 0 → require passes → continue
            have hfailEval' : evalIRExpr state failCond = some 0 := by
              have : SourceSemantics.evalExpr fields runtime cond ≠ some 0 := by
                rw [hCondSrc]; simp [hzero]
              simpa [this, SourceSemantics.boolWord] using hfailEval
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
            simp [hzero, hirExec]
            constructor
            · simpa [hirExec] using htailSem
            · simpa [hirExec] using htailExact
  | return_ hvalue hinScope hrest ih =>
      rename_i scope value rest
      have hpresent : exprBoundNamesPresent value runtime.bindings :=
        exprBoundNamesPresent_of_scope hscope hinScope
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      -- Establish that evalExpr value is some, using eval_compileExpr_core
      have heval := eval_compileExpr_core hvalue hexact hbounded hpresent hruntime
      rw [hvalueIR] at heval; simp [Except.toOption] at heval
      rcases hIR : evalIRExpr state valueIR with _ | retVal
      · simp [hIR, Option.bind] at heval
      · simp [hIR, Option.bind] at heval
        have hEvalSrc : SourceSemantics.evalExpr fields runtime value = some retVal :=
          heval.symm
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
        · have hruntime' : runtimeStateMatchesIR fields runtime state' :=
            runtimeStateMatchesIR_setMemory hruntime 0 retVal
          have hexact' : bindingsExactlyMatchIRVars runtime.bindings state' :=
            bindingsExactlyMatchIRVars_setMemory hexact 0 retVal
          have hmstore :
              execIRStmt (tailIR.length + 2) state
                (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])) =
                .continue state' := by
            simp [execIRStmt, evalIRExpr, hIR, state']
          have hreturn :
              execIRStmt (tailIR.length + 1) state'
                (YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])) =
                .return retVal state' := by
            simp [execIRStmt, evalIRExpr, state']
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
          rw [SourceSemantics.execStmtList, SourceSemantics.execStmt, hEvalSrc]
          dsimp [state']
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
-- SORRY'D:   induction hcore generalizing runtime state inScopeNames with
-- SORRY'D:   | nil =>
-- SORRY'D:       refine ⟨[], rfl, ?_⟩
-- SORRY'D:       constructor
-- SORRY'D:       · simpa [SourceSemantics.execStmtList, execIRStmts, stmtResultMatchesIRExec] using hruntime
-- SORRY'D:       · simpa [SourceSemantics.execStmtList, execIRStmts, stmtResultMatchesIRExecExact] using
-- SORRY'D:           And.intro hexact hbounded
-- SORRY'D:   | letVar hvalue hinScope hrest ih =>
-- SORRY'D:       rename_i scope name value rest
-- SORRY'D:       have hpresent : exprBoundNamesPresent value runtime.bindings :=
-- SORRY'D:         exprBoundNamesPresent_of_scope hscope hinScope
-- SORRY'D:       rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
-- SORRY'D:       let valueNat := SourceSemantics.evalExpr fields runtime value
-- SORRY'D:       let runtime' :=
-- SORRY'D:         { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
-- SORRY'D:       let state' := state.setVar name valueNat
-- SORRY'D:       have heval := eval_compileExpr_core hvalue hexact hbounded hpresent hruntime
-- SORRY'D:       rw [hvalueIR] at heval
-- SORRY'D:       have heval' : evalIRExpr state valueIR = some valueNat := by
-- SORRY'D:         simpa [valueNat] using heval
-- SORRY'D:       have hvalueLt := evalExpr_lt_evmModulus_core hvalue hexact hbounded hpresent hruntime
-- SORRY'D:       have hruntime' : runtimeStateMatchesIR fields runtime' state' :=
-- SORRY'D:         runtimeStateMatchesIR_setVar_bindValue hruntime name valueNat
-- SORRY'D:       have hexact' : bindingsExactlyMatchIRVars runtime'.bindings state' :=
-- SORRY'D:         bindingsExactlyMatchIRVars_setVar_bindValue hexact name valueNat
-- SORRY'D:       have hbounded' : bindingsBounded runtime'.bindings :=
-- SORRY'D:         bindingsBounded_bindValue hbounded name valueNat hvalueLt
-- SORRY'D:       have hscope' : scopeNamesPresent (name :: scope) runtime'.bindings :=
-- SORRY'D:         scopeNamesPresent_cons_bindValue hscope
-- SORRY'D:       rcases ih (runtime := runtime') (state := state')
-- SORRY'D:           (inScopeNames := collectStmtNames (.letVar name value) ++ inScopeNames)
-- SORRY'D:           hscope' hexact' hbounded' hruntime' with
-- SORRY'D:         ⟨tailIR, htailCompile, htailSem, htailExact⟩
-- SORRY'D:       refine ⟨[YulStmt.let_ name valueIR] ++ tailIR, ?_, ?_⟩
-- SORRY'D:       · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
-- SORRY'D:         rw [hvalueIR]
-- SORRY'D:         simp [htailCompile]
-- SORRY'D:         exact rfl
-- SORRY'D:       · have hstmt :
-- SORRY'D:             execIRStmt (tailIR.length + 1) state (YulStmt.let_ name valueIR) =
-- SORRY'D:               .continue state' := by
-- SORRY'D:           simp [execIRStmt, heval', state', valueNat]
-- SORRY'D:         have hirExec :
-- SORRY'D:             execIRStmts (tailIR.length + 2) state
-- SORRY'D:               (YulStmt.let_ name valueIR :: tailIR) =
-- SORRY'D:               execIRStmts (tailIR.length + 1) state' tailIR := by
-- SORRY'D:           simpa using
-- SORRY'D:             (execIRStmts_cons_of_execIRStmt_continue state state'
-- SORRY'D:               (YulStmt.let_ name valueIR) tailIR hstmt)
-- SORRY'D:         rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
-- SORRY'D:         dsimp [runtime', state']
-- SORRY'D:         constructor
-- SORRY'D:         · simpa [hirExec, runtime', valueNat] using htailSem
-- SORRY'D:         · simpa [hirExec, runtime', valueNat] using htailExact
-- SORRY'D:   | assignVar hvalue hinScope hrest ih =>
-- SORRY'D:       rename_i scope name value rest
-- SORRY'D:       have hpresent : exprBoundNamesPresent value runtime.bindings :=
-- SORRY'D:         exprBoundNamesPresent_of_scope hscope hinScope
-- SORRY'D:       rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
-- SORRY'D:       let valueNat := SourceSemantics.evalExpr fields runtime value
-- SORRY'D:       let runtime' :=
-- SORRY'D:         { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
-- SORRY'D:       let state' := state.setVar name valueNat
-- SORRY'D:       have heval := eval_compileExpr_core hvalue hexact hbounded hpresent hruntime
-- SORRY'D:       rw [hvalueIR] at heval
-- SORRY'D:       have heval' : evalIRExpr state valueIR = some valueNat := by
-- SORRY'D:         simpa [valueNat] using heval
-- SORRY'D:       have hvalueLt := evalExpr_lt_evmModulus_core hvalue hexact hbounded hpresent hruntime
-- SORRY'D:       have hruntime' : runtimeStateMatchesIR fields runtime' state' :=
-- SORRY'D:         runtimeStateMatchesIR_setVar_bindValue hruntime name valueNat
-- SORRY'D:       have hexact' : bindingsExactlyMatchIRVars runtime'.bindings state' :=
-- SORRY'D:         bindingsExactlyMatchIRVars_setVar_bindValue hexact name valueNat
-- SORRY'D:       have hbounded' : bindingsBounded runtime'.bindings :=
-- SORRY'D:         bindingsBounded_bindValue hbounded name valueNat hvalueLt
-- SORRY'D:       have hscope' : scopeNamesPresent (name :: scope) runtime'.bindings :=
-- SORRY'D:         scopeNamesPresent_cons_bindValue hscope
-- SORRY'D:       rcases ih (runtime := runtime') (state := state')
-- SORRY'D:           (inScopeNames := collectStmtNames (.assignVar name value) ++ inScopeNames)
-- SORRY'D:           hscope' hexact' hbounded' hruntime' with
-- SORRY'D:         ⟨tailIR, htailCompile, htailSem, htailExact⟩
-- SORRY'D:       refine ⟨[YulStmt.assign name valueIR] ++ tailIR, ?_, ?_⟩
-- SORRY'D:       · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
-- SORRY'D:         rw [hvalueIR]
-- SORRY'D:         simp [htailCompile]
-- SORRY'D:         exact rfl
-- SORRY'D:       · have hstmt :
-- SORRY'D:             execIRStmt (tailIR.length + 1) state (YulStmt.assign name valueIR) =
-- SORRY'D:               .continue state' := by
-- SORRY'D:           simp [execIRStmt, heval', state', valueNat]
-- SORRY'D:         have hirExec :
-- SORRY'D:             execIRStmts (tailIR.length + 2) state
-- SORRY'D:               (YulStmt.assign name valueIR :: tailIR) =
-- SORRY'D:               execIRStmts (tailIR.length + 1) state' tailIR := by
-- SORRY'D:           simpa using
-- SORRY'D:             (execIRStmts_cons_of_execIRStmt_continue state state'
-- SORRY'D:               (YulStmt.assign name valueIR) tailIR hstmt)
-- SORRY'D:         rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
-- SORRY'D:         dsimp [runtime', state']
-- SORRY'D:         constructor
-- SORRY'D:         · simpa [hirExec, runtime', valueNat] using htailSem
-- SORRY'D:         · simpa [hirExec, runtime', valueNat] using htailExact
-- SORRY'D:   | require_ hcond hinScope hrest ih =>
-- SORRY'D:       rename_i scope cond message rest
-- SORRY'D:       have hpresent : exprBoundNamesPresent cond runtime.bindings :=
-- SORRY'D:         exprBoundNamesPresent_of_scope hscope hinScope
-- SORRY'D:       rcases eval_compileRequireFailCond_core hcond hexact hbounded hpresent hruntime with
-- SORRY'D:         ⟨failCond, hfailCompile, hfailEval⟩
-- SORRY'D:       rcases ih (runtime := runtime) (state := state)
-- SORRY'D:           (inScopeNames := collectStmtNames (.require cond message) ++ inScopeNames)
-- SORRY'D:           hscope hexact hbounded hruntime with
-- SORRY'D:         ⟨tailIR, htailCompile, htailSem, htailExact⟩
-- SORRY'D:       refine ⟨[YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR, ?_, ?_⟩
-- SORRY'D:       · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
-- SORRY'D:         rw [hfailCompile]
-- SORRY'D:         simp [htailCompile]
-- SORRY'D:         exact rfl
-- SORRY'D:       · by_cases hcondZero : SourceSemantics.evalExpr fields runtime cond = 0
-- SORRY'D:         · rcases execIRStmts_revertWithMessage_revert (fuel := tailIR.length) (state := state) message with
-- SORRY'D:             ⟨revState, hrev⟩
-- SORRY'D:           have hfailEval' : evalIRExpr state failCond = some 1 := by
-- SORRY'D:             simpa [hcondZero, SourceSemantics.boolWord] using hfailEval
-- SORRY'D:           have hstmt :
-- SORRY'D:               execIRStmt (tailIR.length + 1) state
-- SORRY'D:                 (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) =
-- SORRY'D:                   .revert revState := by
-- SORRY'D:             simp [execIRStmt, hfailEval', hrev]
-- SORRY'D:           have hirExec :
-- SORRY'D:               execIRStmts (tailIR.length + 2) state
-- SORRY'D:                 (YulStmt.if_ failCond (CompilationModel.revertWithMessage message) :: tailIR) =
-- SORRY'D:                   .revert revState := by
-- SORRY'D:             simpa using
-- SORRY'D:               (execIRStmts_cons_of_execIRStmt_revert state revState
-- SORRY'D:                 (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) tailIR hstmt)
-- SORRY'D:           rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
-- SORRY'D:           simp [hcondZero, hirExec, stmtResultMatchesIRExec, stmtResultMatchesIRExecExact]
-- SORRY'D:         · have hfailEval' : evalIRExpr state failCond = some 0 := by
-- SORRY'D:             simpa [hcondZero, SourceSemantics.boolWord] using hfailEval
-- SORRY'D:           have hstmt :
-- SORRY'D:               execIRStmt (tailIR.length + 1) state
-- SORRY'D:                 (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) =
-- SORRY'D:                   .continue state := by
-- SORRY'D:             simp [execIRStmt, hfailEval']
-- SORRY'D:           have hirExec :
-- SORRY'D:               execIRStmts (tailIR.length + 2) state
-- SORRY'D:                 (YulStmt.if_ failCond (CompilationModel.revertWithMessage message) :: tailIR) =
-- SORRY'D:                   execIRStmts (tailIR.length + 1) state tailIR := by
-- SORRY'D:             simpa using
-- SORRY'D:               (execIRStmts_cons_of_execIRStmt_continue state state
-- SORRY'D:                 (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) tailIR hstmt)
-- SORRY'D:           rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
-- SORRY'D:           simp [hcondZero, hirExec]
-- SORRY'D:           constructor
-- SORRY'D:           · simpa [hirExec] using htailSem
-- SORRY'D:           · simpa [hirExec] using htailExact
-- SORRY'D:   | return_ hvalue hinScope hrest ih =>
-- SORRY'D:       rename_i scope value rest
-- SORRY'D:       have hpresent : exprBoundNamesPresent value runtime.bindings :=
-- SORRY'D:         exprBoundNamesPresent_of_scope hscope hinScope
-- SORRY'D:       rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
-- SORRY'D:       let retVal := SourceSemantics.evalExpr fields runtime value
-- SORRY'D:       let state' := { state with memory := fun o => if o = 0 then retVal else state.memory o }
-- SORRY'D:       rcases ih (runtime := runtime) (state := state')
-- SORRY'D:           (inScopeNames := collectStmtNames (.return value) ++ inScopeNames)
-- SORRY'D:           hscope
-- SORRY'D:           (bindingsExactlyMatchIRVars_setMemory hexact 0 retVal)
-- SORRY'D:           hbounded
-- SORRY'D:           (runtimeStateMatchesIR_setMemory hruntime 0 retVal) with
-- SORRY'D:         ⟨tailIR, htailCompile, htailSem, htailExact⟩
-- SORRY'D:       refine ⟨[ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
-- SORRY'D:               , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++ tailIR,
-- SORRY'D:         ?_, ?_⟩
-- SORRY'D:       · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
-- SORRY'D:         rw [hvalueIR]
-- SORRY'D:         simp [htailCompile]
-- SORRY'D:         exact rfl
-- SORRY'D:       · have heval := eval_compileExpr_core hvalue hexact hbounded hpresent hruntime
-- SORRY'D:         rw [hvalueIR] at heval
-- SORRY'D:         have heval' : evalIRExpr state valueIR = some retVal := by
-- SORRY'D:           simpa [retVal] using heval
-- SORRY'D:         have hruntime' : runtimeStateMatchesIR fields runtime state' :=
-- SORRY'D:           runtimeStateMatchesIR_setMemory hruntime 0 retVal
-- SORRY'D:         have hexact' : bindingsExactlyMatchIRVars runtime.bindings state' :=
-- SORRY'D:           bindingsExactlyMatchIRVars_setMemory hexact 0 retVal
-- SORRY'D:         have hmstore :
-- SORRY'D:             execIRStmt (tailIR.length + 2) state
-- SORRY'D:               (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])) =
-- SORRY'D:               .continue state' := by
-- SORRY'D:           simp [execIRStmt, evalIRExpr, heval', retVal, state']
-- SORRY'D:         have hreturn :
-- SORRY'D:             execIRStmt (tailIR.length + 1) state'
-- SORRY'D:               (YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])) =
-- SORRY'D:               .return retVal state' := by
-- SORRY'D:           simp [execIRStmt, evalIRExpr, retVal, state']
-- SORRY'D:         have hirExec :
-- SORRY'D:             execIRStmts (tailIR.length + 3)
-- SORRY'D:               state
-- SORRY'D:               (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR]) ::
-- SORRY'D:                 YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ::
-- SORRY'D:                 tailIR) =
-- SORRY'D:               .return retVal state' := by
-- SORRY'D:           simpa using
-- SORRY'D:             (execIRStmts_two_of_continue_then_return state state' state'
-- SORRY'D:               (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR]))
-- SORRY'D:               (YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]))
-- SORRY'D:               tailIR retVal hmstore hreturn)
-- SORRY'D:         rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
-- SORRY'D:         dsimp [retVal, state']
-- SORRY'D:         constructor
-- SORRY'D:         · simpa [hirExec] using (show
-- SORRY'D:             stmtResultMatchesIRExec fields
-- SORRY'D:               (SourceSemantics.StmtResult.return retVal runtime)
-- SORRY'D:               (.return retVal state') from ⟨rfl, hruntime'⟩)
-- SORRY'D:         · simpa [hirExec] using (show
-- SORRY'D:             stmtResultMatchesIRExecExact
-- SORRY'D:               (SourceSemantics.StmtResult.return retVal runtime)
-- SORRY'D:               (.return retVal state') from ⟨hexact', hbounded⟩)
-- SORRY'D:   | stop hrest ih =>
-- SORRY'D:       rename_i scope rest
-- SORRY'D:       rcases ih (runtime := runtime) (state := state)
-- SORRY'D:           (inScopeNames := collectStmtNames (.stop) ++ inScopeNames)
-- SORRY'D:           hscope hexact hbounded hruntime with
-- SORRY'D:         ⟨tailIR, htailCompile, htailSem, htailExact⟩
-- SORRY'D:       refine ⟨[YulStmt.expr (YulExpr.call "stop" [])] ++ tailIR, ?_, ?_⟩
-- SORRY'D:       · simpa [CompilationModel.compileStmtList, CompilationModel.compileStmt, htailCompile]
-- SORRY'D:       · have hstmt :
-- SORRY'D:             execIRStmt (tailIR.length + 1) state (YulStmt.expr (YulExpr.call "stop" [])) =
-- SORRY'D:               .stop state := by
-- SORRY'D:           simp [execIRStmt]
-- SORRY'D:         have hirExec :
-- SORRY'D:             execIRStmts (tailIR.length + 2) state
-- SORRY'D:               (YulStmt.expr (YulExpr.call "stop" []) :: tailIR) =
-- SORRY'D:               .stop state := by
-- SORRY'D:           simpa using
-- SORRY'D:             (execIRStmts_cons_of_execIRStmt_stop state state
-- SORRY'D:               (YulStmt.expr (YulExpr.call "stop" [])) tailIR hstmt)
-- SORRY'D:         rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
-- SORRY'D:         simp [hirExec]
-- SORRY'D:         exact ⟨hruntime, ⟨hexact, hbounded⟩⟩

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
      have heval := eval_compileExpr_core hvalue hexact hbounded hpresent hruntime
      rw [hvalueIR] at heval; simp [Except.toOption] at heval
      rcases hIR : evalIRExpr state valueIR with _ | valueNat
      · simp [hIR, Option.bind] at heval
      · simp [hIR, Option.bind] at heval
        have hEvalSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
          heval.symm
        let runtime' :=
          { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
        let state' := state.setVar name valueNat
        have hvalueLt := evalExpr_lt_evmModulus_core hvalue hexact hbounded hpresent hruntime
        rw [hEvalSrc] at hvalueLt; simp at hvalueLt
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
            simp [execIRStmt, hIR, state']
          have hirExec :
              execIRStmts (tailIR.length + extraFuel + 2) state
                (YulStmt.let_ name valueIR :: tailIR) =
                execIRStmts (tailIR.length + extraFuel + 1) state' tailIR := by
            simpa using
              (execIRStmts_cons_of_execIRStmt_continue_extraFuel extraFuel state state'
                (YulStmt.let_ name valueIR) tailIR hstmt)
          rw [SourceSemantics.execStmtList, SourceSemantics.execStmt, hEvalSrc]
          dsimp [runtime', state']
          constructor
          · have hirExec' :
                execIRStmts (tailIR.length + 1 + extraFuel + 1) state
                  (YulStmt.let_ name valueIR :: tailIR) =
                  execIRStmts (tailIR.length + extraFuel + 1) state' tailIR := by
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hirExec
            rw [hirExec']
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, runtime'] using htailSem
          · have hirExec' :
                execIRStmts (tailIR.length + 1 + extraFuel + 1) state
                  (YulStmt.let_ name valueIR :: tailIR) =
                  execIRStmts (tailIR.length + extraFuel + 1) state' tailIR := by
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hirExec
            rw [hirExec']
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, runtime'] using htailExact
  | assignVar hvalue hinScope hrest ih =>
      rename_i scope name value rest
      have hpresent : exprBoundNamesPresent value runtime.bindings :=
        exprBoundNamesPresent_of_scope hscope hinScope
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      have heval := eval_compileExpr_core hvalue hexact hbounded hpresent hruntime
      rw [hvalueIR] at heval; simp [Except.toOption] at heval
      rcases hIR : evalIRExpr state valueIR with _ | valueNat
      · simp [hIR, Option.bind] at heval
      · simp [hIR, Option.bind] at heval
        have hEvalSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
          heval.symm
        let runtime' :=
          { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
        let state' := state.setVar name valueNat
        have hvalueLt := evalExpr_lt_evmModulus_core hvalue hexact hbounded hpresent hruntime
        rw [hEvalSrc] at hvalueLt; simp at hvalueLt
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
            simp [execIRStmt, hIR, state']
          have hirExec :
              execIRStmts (tailIR.length + extraFuel + 2) state
                (YulStmt.assign name valueIR :: tailIR) =
                execIRStmts (tailIR.length + extraFuel + 1) state' tailIR := by
            simpa using
              (execIRStmts_cons_of_execIRStmt_continue_extraFuel extraFuel state state'
                (YulStmt.assign name valueIR) tailIR hstmt)
          rw [SourceSemantics.execStmtList, SourceSemantics.execStmt, hEvalSrc]
          dsimp [runtime', state']
          constructor
          · have hirExec' :
                execIRStmts (tailIR.length + 1 + extraFuel + 1) state
                  (YulStmt.assign name valueIR :: tailIR) =
                  execIRStmts (tailIR.length + extraFuel + 1) state' tailIR := by
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hirExec
            rw [hirExec']
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, runtime'] using htailSem
          · have hirExec' :
                execIRStmts (tailIR.length + 1 + extraFuel + 1) state
                  (YulStmt.assign name valueIR :: tailIR) =
                  execIRStmts (tailIR.length + extraFuel + 1) state' tailIR := by
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hirExec
            rw [hirExec']
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, runtime'] using htailExact
  | require_ hcond hinScope hrest ih =>
      rename_i scope cond message rest
      have hpresent : exprBoundNamesPresent cond runtime.bindings :=
        exprBoundNamesPresent_of_scope hscope hinScope
      -- First, establish that evalExpr cond is some, using eval_compileExpr_core
      rcases compileExpr_core_ok hcond with ⟨condIR, hcondIR⟩
      have hCondEval := eval_compileExpr_core hcond hexact hbounded hpresent hruntime
      rw [hcondIR] at hCondEval; simp [Except.toOption] at hCondEval
      rcases hCondIRVal : evalIRExpr state condIR with _ | condVal
      · simp [hCondIRVal, Option.bind] at hCondEval
      · simp [hCondIRVal, Option.bind] at hCondEval
        have hCondSrc : SourceSemantics.evalExpr fields runtime cond = some condVal :=
          hCondEval.symm
        -- Get the fail condition IR
        rcases eval_compileRequireFailCond_core_onExpr hcond
            (bindingsExactlyMatchIRVars_implies_onExpr hexact)
            hbounded hpresent hruntime with
          ⟨failCond, hfailCompile, hfailEval⟩
        rcases ih (runtime := runtime) (state := state)
            (inScopeNames := collectStmtNames (.require cond message) ++ inScopeNames)
            hscope hexact hbounded hruntime with
          ⟨tailIR, htailCompile, htailSem, htailExact⟩
        refine ⟨[YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR,
          ?_, ?_⟩
        · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
          rw [hfailCompile]
          simp [htailCompile]
          exact rfl
        · rw [SourceSemantics.execStmtList, SourceSemantics.execStmt, hCondSrc]
          by_cases hzero : condVal = 0
          · -- condVal = 0 → require fails → revert
            rcases execIRStmts_revertWithMessage_revert (fuel := tailIR.length + extraFuel)
                (state := state) message with
              ⟨revState, hrev⟩
            have hfailEval' : evalIRExpr state failCond = some 1 := by
              rw [hCondSrc, hzero] at hfailEval
              simpa [SourceSemantics.boolWord] using hfailEval
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
                  (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) tailIR
                  hstmt)
            have hirExec' :
                execIRStmts (tailIR.length + 1 + extraFuel + 1) state
                  (YulStmt.if_ failCond (CompilationModel.revertWithMessage message) :: tailIR) =
                    .revert revState := by
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hirExec
            simp [hzero, hirExec', stmtResultMatchesIRExec, stmtResultMatchesIRExecExact]
          · -- condVal ≠ 0 → require passes → continue
            have hfailEval' : evalIRExpr state failCond = some 0 := by
              have : SourceSemantics.evalExpr fields runtime cond ≠ some 0 := by
                rw [hCondSrc]; simp [hzero]
              simpa [this, SourceSemantics.boolWord] using hfailEval
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
                  (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) tailIR
                  hstmt)
            have hirExec' :
                execIRStmts (tailIR.length + 1 + extraFuel + 1) state
                  (YulStmt.if_ failCond (CompilationModel.revertWithMessage message) :: tailIR) =
                    execIRStmts (tailIR.length + extraFuel + 1) state tailIR := by
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hirExec
            simp [hzero, hirExec']
            constructor
            · exact htailSem
            · exact htailExact
  | return_ hvalue hinScope hrest ih =>
      rename_i scope value rest
      have hpresent : exprBoundNamesPresent value runtime.bindings :=
        exprBoundNamesPresent_of_scope hscope hinScope
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      -- Establish that evalExpr value is some, using eval_compileExpr_core
      have heval := eval_compileExpr_core hvalue hexact hbounded hpresent hruntime
      rw [hvalueIR] at heval; simp [Except.toOption] at heval
      rcases hIR : evalIRExpr state valueIR with _ | retVal
      · simp [hIR, Option.bind] at heval
      · simp [hIR, Option.bind] at heval
        have hEvalSrc : SourceSemantics.evalExpr fields runtime value = some retVal :=
          heval.symm
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
        · have hruntime' : runtimeStateMatchesIR fields runtime state' :=
            runtimeStateMatchesIR_setMemory hruntime 0 retVal
          have hexact' : bindingsExactlyMatchIRVars runtime.bindings state' :=
            bindingsExactlyMatchIRVars_setMemory hexact 0 retVal
          have hmstore :
              execIRStmt (tailIR.length + extraFuel + 2) state
                (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])) =
                .continue state' := by
            simp [execIRStmt, evalIRExpr, hIR, state']
          have hreturn :
              execIRStmt (tailIR.length + extraFuel + 1) state'
                (YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])) =
                .return retVal state' := by
            simp [execIRStmt, evalIRExpr, state']
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
          rw [SourceSemantics.execStmtList, SourceSemantics.execStmt, hEvalSrc]
          dsimp [state']
          constructor
          · simpa [hirExec'] using (show
              stmtResultMatchesIRExec fields
                (SourceSemantics.StmtResult.return retVal runtime)
                (.return retVal state') from ⟨rfl, hruntime'⟩)
          · simpa [hirExec'] using (show
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
        simp [hirExec']
        exact ⟨hruntime, ⟨hexact, hbounded⟩⟩
-- SORRY'D:   induction hcore generalizing runtime state inScopeNames with
-- SORRY'D:   | nil =>
-- SORRY'D:       refine ⟨[], rfl, ?_⟩
-- SORRY'D:       constructor
-- SORRY'D:       · simpa [SourceSemantics.execStmtList, execIRStmts, stmtResultMatchesIRExec] using hruntime
-- SORRY'D:       · simpa [SourceSemantics.execStmtList, execIRStmts, stmtResultMatchesIRExecExact] using
-- SORRY'D:           And.intro hexact hbounded
-- SORRY'D:   | letVar hvalue hinScope hrest ih =>
-- SORRY'D:       rename_i scope name value rest
-- SORRY'D:       have hpresent : exprBoundNamesPresent value runtime.bindings :=
-- SORRY'D:         exprBoundNamesPresent_of_scope hscope hinScope
-- SORRY'D:       rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
-- SORRY'D:       let valueNat := SourceSemantics.evalExpr fields runtime value
-- SORRY'D:       let runtime' :=
-- SORRY'D:         { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
-- SORRY'D:       let state' := state.setVar name valueNat
-- SORRY'D:       have heval := eval_compileExpr_core hvalue hexact hbounded hpresent hruntime
-- SORRY'D:       rw [hvalueIR] at heval
-- SORRY'D:       have heval' : evalIRExpr state valueIR = some valueNat := by
-- SORRY'D:         simpa [valueNat] using heval
-- SORRY'D:       have hvalueLt := evalExpr_lt_evmModulus_core hvalue hexact hbounded hpresent hruntime
-- SORRY'D:       have hruntime' : runtimeStateMatchesIR fields runtime' state' :=
-- SORRY'D:         runtimeStateMatchesIR_setVar_bindValue hruntime name valueNat
-- SORRY'D:       have hexact' : bindingsExactlyMatchIRVars runtime'.bindings state' :=
-- SORRY'D:         bindingsExactlyMatchIRVars_setVar_bindValue hexact name valueNat
-- SORRY'D:       have hbounded' : bindingsBounded runtime'.bindings :=
-- SORRY'D:         bindingsBounded_bindValue hbounded name valueNat hvalueLt
-- SORRY'D:       have hscope' : scopeNamesPresent (name :: scope) runtime'.bindings :=
-- SORRY'D:         scopeNamesPresent_cons_bindValue hscope
-- SORRY'D:       rcases ih (runtime := runtime') (state := state')
-- SORRY'D:           (inScopeNames := collectStmtNames (.letVar name value) ++ inScopeNames)
-- SORRY'D:           hscope' hexact' hbounded' hruntime' with
-- SORRY'D:         ⟨tailIR, htailCompile, htailSem, htailExact⟩
-- SORRY'D:       refine ⟨[YulStmt.let_ name valueIR] ++ tailIR, ?_, ?_⟩
-- SORRY'D:       · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
-- SORRY'D:         rw [hvalueIR]
-- SORRY'D:         simp [htailCompile]
-- SORRY'D:         exact rfl
-- SORRY'D:       · have hstmt :
-- SORRY'D:             execIRStmt (tailIR.length + extraFuel + 1) state (YulStmt.let_ name valueIR) =
-- SORRY'D:               .continue state' := by
-- SORRY'D:           simp [execIRStmt, heval', state', valueNat]
-- SORRY'D:         have hirExec :
-- SORRY'D:             execIRStmts (tailIR.length + extraFuel + 2) state
-- SORRY'D:               (YulStmt.let_ name valueIR :: tailIR) =
-- SORRY'D:               execIRStmts (tailIR.length + extraFuel + 1) state' tailIR := by
-- SORRY'D:           simpa using
-- SORRY'D:             (execIRStmts_cons_of_execIRStmt_continue_extraFuel extraFuel state state'
-- SORRY'D:               (YulStmt.let_ name valueIR) tailIR hstmt)
-- SORRY'D:         rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
-- SORRY'D:         dsimp [runtime', state']
-- SORRY'D:         constructor
-- SORRY'D:         · have hirExec' :
-- SORRY'D:               execIRStmts (tailIR.length + 1 + extraFuel + 1) state
-- SORRY'D:                 (YulStmt.let_ name valueIR :: tailIR) =
-- SORRY'D:                 execIRStmts (tailIR.length + extraFuel + 1) state' tailIR := by
-- SORRY'D:             simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hirExec
-- SORRY'D:           rw [hirExec']
-- SORRY'D:           simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, runtime', valueNat] using htailSem
-- SORRY'D:         · have hirExec' :
-- SORRY'D:               execIRStmts (tailIR.length + 1 + extraFuel + 1) state
-- SORRY'D:                 (YulStmt.let_ name valueIR :: tailIR) =
-- SORRY'D:                 execIRStmts (tailIR.length + extraFuel + 1) state' tailIR := by
-- SORRY'D:             simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hirExec
-- SORRY'D:           rw [hirExec']
-- SORRY'D:           simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, runtime', valueNat] using htailExact
-- SORRY'D:   | assignVar hvalue hinScope hrest ih =>
-- SORRY'D:       rename_i scope name value rest
-- SORRY'D:       have hpresent : exprBoundNamesPresent value runtime.bindings :=
-- SORRY'D:         exprBoundNamesPresent_of_scope hscope hinScope
-- SORRY'D:       rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
-- SORRY'D:       let valueNat := SourceSemantics.evalExpr fields runtime value
-- SORRY'D:       let runtime' :=
-- SORRY'D:         { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
-- SORRY'D:       let state' := state.setVar name valueNat
-- SORRY'D:       have heval := eval_compileExpr_core hvalue hexact hbounded hpresent hruntime
-- SORRY'D:       rw [hvalueIR] at heval
-- SORRY'D:       have heval' : evalIRExpr state valueIR = some valueNat := by
-- SORRY'D:         simpa [valueNat] using heval
-- SORRY'D:       have hvalueLt := evalExpr_lt_evmModulus_core hvalue hexact hbounded hpresent hruntime
-- SORRY'D:       have hruntime' : runtimeStateMatchesIR fields runtime' state' :=
-- SORRY'D:         runtimeStateMatchesIR_setVar_bindValue hruntime name valueNat
-- SORRY'D:       have hexact' : bindingsExactlyMatchIRVars runtime'.bindings state' :=
-- SORRY'D:         bindingsExactlyMatchIRVars_setVar_bindValue hexact name valueNat
-- SORRY'D:       have hbounded' : bindingsBounded runtime'.bindings :=
-- SORRY'D:         bindingsBounded_bindValue hbounded name valueNat hvalueLt
-- SORRY'D:       have hscope' : scopeNamesPresent (name :: scope) runtime'.bindings :=
-- SORRY'D:         scopeNamesPresent_cons_bindValue hscope
-- SORRY'D:       rcases ih (runtime := runtime') (state := state')
-- SORRY'D:           (inScopeNames := collectStmtNames (.assignVar name value) ++ inScopeNames)
-- SORRY'D:           hscope' hexact' hbounded' hruntime' with
-- SORRY'D:         ⟨tailIR, htailCompile, htailSem, htailExact⟩
-- SORRY'D:       refine ⟨[YulStmt.assign name valueIR] ++ tailIR, ?_, ?_⟩
-- SORRY'D:       · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
-- SORRY'D:         rw [hvalueIR]
-- SORRY'D:         simp [htailCompile]
-- SORRY'D:         exact rfl
-- SORRY'D:       · have hstmt :
-- SORRY'D:             execIRStmt (tailIR.length + extraFuel + 1) state (YulStmt.assign name valueIR) =
-- SORRY'D:               .continue state' := by
-- SORRY'D:           simp [execIRStmt, heval', state', valueNat]
-- SORRY'D:         have hirExec :
-- SORRY'D:             execIRStmts (tailIR.length + extraFuel + 2) state
-- SORRY'D:               (YulStmt.assign name valueIR :: tailIR) =
-- SORRY'D:               execIRStmts (tailIR.length + extraFuel + 1) state' tailIR := by
-- SORRY'D:           simpa using
-- SORRY'D:             (execIRStmts_cons_of_execIRStmt_continue_extraFuel extraFuel state state'
-- SORRY'D:               (YulStmt.assign name valueIR) tailIR hstmt)
-- SORRY'D:         rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
-- SORRY'D:         dsimp [runtime', state']
-- SORRY'D:         constructor
-- SORRY'D:         · have hirExec' :
-- SORRY'D:               execIRStmts (tailIR.length + 1 + extraFuel + 1) state
-- SORRY'D:                 (YulStmt.assign name valueIR :: tailIR) =
-- SORRY'D:                 execIRStmts (tailIR.length + extraFuel + 1) state' tailIR := by
-- SORRY'D:             simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hirExec
-- SORRY'D:           rw [hirExec']
-- SORRY'D:           simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, runtime', valueNat] using htailSem
-- SORRY'D:         · have hirExec' :
-- SORRY'D:               execIRStmts (tailIR.length + 1 + extraFuel + 1) state
-- SORRY'D:                 (YulStmt.assign name valueIR :: tailIR) =
-- SORRY'D:                 execIRStmts (tailIR.length + extraFuel + 1) state' tailIR := by
-- SORRY'D:             simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hirExec
-- SORRY'D:           rw [hirExec']
-- SORRY'D:           simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, runtime', valueNat] using htailExact
-- SORRY'D:   | require_ hcond hinScope hrest ih =>
-- SORRY'D:       rename_i scope cond message rest
-- SORRY'D:       have hpresent : exprBoundNamesPresent cond runtime.bindings :=
-- SORRY'D:         exprBoundNamesPresent_of_scope hscope hinScope
-- SORRY'D:       rcases eval_compileRequireFailCond_core hcond hexact hbounded hpresent hruntime with
-- SORRY'D:         ⟨failCond, hfailCompile, hfailEval⟩
-- SORRY'D:       rcases ih (runtime := runtime) (state := state)
-- SORRY'D:           (inScopeNames := collectStmtNames (.require cond message) ++ inScopeNames)
-- SORRY'D:           hscope hexact hbounded hruntime with
-- SORRY'D:         ⟨tailIR, htailCompile, htailSem, htailExact⟩
-- SORRY'D:       refine ⟨[YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR, ?_, ?_⟩
-- SORRY'D:       · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
-- SORRY'D:         rw [hfailCompile]
-- SORRY'D:         simp [htailCompile]
-- SORRY'D:         exact rfl
-- SORRY'D:       · by_cases hcondZero : SourceSemantics.evalExpr fields runtime cond = 0
-- SORRY'D:         · rcases execIRStmts_revertWithMessage_revert (fuel := tailIR.length + extraFuel)
-- SORRY'D:             (state := state) message with
-- SORRY'D:             ⟨revState, hrev⟩
-- SORRY'D:           have hfailEval' : evalIRExpr state failCond = some 1 := by
-- SORRY'D:             simpa [hcondZero, SourceSemantics.boolWord] using hfailEval
-- SORRY'D:           have hstmt :
-- SORRY'D:               execIRStmt (tailIR.length + extraFuel + 1) state
-- SORRY'D:                 (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) =
-- SORRY'D:                   .revert revState := by
-- SORRY'D:             simp [execIRStmt, hfailEval', hrev]
-- SORRY'D:           have hirExec :
-- SORRY'D:               execIRStmts (tailIR.length + extraFuel + 2) state
-- SORRY'D:                 (YulStmt.if_ failCond (CompilationModel.revertWithMessage message) :: tailIR) =
-- SORRY'D:                   .revert revState := by
-- SORRY'D:             simpa using
-- SORRY'D:               (execIRStmts_cons_of_execIRStmt_revert_extraFuel extraFuel state revState
-- SORRY'D:                 (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) tailIR hstmt)
-- SORRY'D:           have hirExec' :
-- SORRY'D:               execIRStmts (tailIR.length + 1 + extraFuel + 1) state
-- SORRY'D:                 (YulStmt.if_ failCond (CompilationModel.revertWithMessage message) :: tailIR) =
-- SORRY'D:                   .revert revState := by
-- SORRY'D:             simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hirExec
-- SORRY'D:           rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
-- SORRY'D:           simp [hcondZero, hirExec', stmtResultMatchesIRExec, stmtResultMatchesIRExecExact]
-- SORRY'D:         · have hfailEval' : evalIRExpr state failCond = some 0 := by
-- SORRY'D:             simpa [hcondZero, SourceSemantics.boolWord] using hfailEval
-- SORRY'D:           have hstmt :
-- SORRY'D:               execIRStmt (tailIR.length + extraFuel + 1) state
-- SORRY'D:                 (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) =
-- SORRY'D:                   .continue state := by
-- SORRY'D:             simp [execIRStmt, hfailEval']
-- SORRY'D:           have hirExec :
-- SORRY'D:               execIRStmts (tailIR.length + extraFuel + 2) state
-- SORRY'D:                 (YulStmt.if_ failCond (CompilationModel.revertWithMessage message) :: tailIR) =
-- SORRY'D:                   execIRStmts (tailIR.length + extraFuel + 1) state tailIR := by
-- SORRY'D:             simpa using
-- SORRY'D:               (execIRStmts_cons_of_execIRStmt_continue_extraFuel extraFuel state state
-- SORRY'D:                 (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) tailIR hstmt)
-- SORRY'D:           have hirExec' :
-- SORRY'D:               execIRStmts (tailIR.length + 1 + extraFuel + 1) state
-- SORRY'D:                 (YulStmt.if_ failCond (CompilationModel.revertWithMessage message) :: tailIR) =
-- SORRY'D:                   execIRStmts (tailIR.length + extraFuel + 1) state tailIR := by
-- SORRY'D:             simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hirExec
-- SORRY'D:           rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
-- SORRY'D:           simp [hcondZero, hirExec']
-- SORRY'D:           constructor
-- SORRY'D:           · exact htailSem
-- SORRY'D:           · exact htailExact
-- SORRY'D:   | return_ hvalue hinScope hrest ih =>
-- SORRY'D:       rename_i scope value rest
-- SORRY'D:       have hpresent : exprBoundNamesPresent value runtime.bindings :=
-- SORRY'D:         exprBoundNamesPresent_of_scope hscope hinScope
-- SORRY'D:       rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
-- SORRY'D:       let retVal := SourceSemantics.evalExpr fields runtime value
-- SORRY'D:       let state' := { state with memory := fun o => if o = 0 then retVal else state.memory o }
-- SORRY'D:       rcases ih (runtime := runtime) (state := state')
-- SORRY'D:           (inScopeNames := collectStmtNames (.return value) ++ inScopeNames)
-- SORRY'D:           hscope
-- SORRY'D:           (bindingsExactlyMatchIRVars_setMemory hexact 0 retVal)
-- SORRY'D:           hbounded
-- SORRY'D:           (runtimeStateMatchesIR_setMemory hruntime 0 retVal) with
-- SORRY'D:         ⟨tailIR, htailCompile, htailSem, htailExact⟩
-- SORRY'D:       refine ⟨[ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
-- SORRY'D:               , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++ tailIR,
-- SORRY'D:         ?_, ?_⟩
-- SORRY'D:       · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
-- SORRY'D:         rw [hvalueIR]
-- SORRY'D:         simp [htailCompile]
-- SORRY'D:         exact rfl
-- SORRY'D:       · have heval := eval_compileExpr_core hvalue hexact hbounded hpresent hruntime
-- SORRY'D:         rw [hvalueIR] at heval
-- SORRY'D:         have heval' : evalIRExpr state valueIR = some retVal := by
-- SORRY'D:           simpa [retVal] using heval
-- SORRY'D:         have hruntime' : runtimeStateMatchesIR fields runtime state' :=
-- SORRY'D:           runtimeStateMatchesIR_setMemory hruntime 0 retVal
-- SORRY'D:         have hexact' : bindingsExactlyMatchIRVars runtime.bindings state' :=
-- SORRY'D:           bindingsExactlyMatchIRVars_setMemory hexact 0 retVal
-- SORRY'D:         have hmstore :
-- SORRY'D:             execIRStmt (tailIR.length + extraFuel + 2) state
-- SORRY'D:               (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])) =
-- SORRY'D:               .continue state' := by
-- SORRY'D:           simp [execIRStmt, evalIRExpr, heval', retVal, state']
-- SORRY'D:         have hreturn :
-- SORRY'D:             execIRStmt (tailIR.length + extraFuel + 1) state'
-- SORRY'D:               (YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])) =
-- SORRY'D:               .return retVal state' := by
-- SORRY'D:           simp [execIRStmt, evalIRExpr, retVal, state']
-- SORRY'D:         have hirExec :
-- SORRY'D:             execIRStmts (tailIR.length + extraFuel + 3)
-- SORRY'D:               state
-- SORRY'D:               (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR]) ::
-- SORRY'D:                 YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ::
-- SORRY'D:                 tailIR) =
-- SORRY'D:               .return retVal state' := by
-- SORRY'D:           simpa using
-- SORRY'D:             (execIRStmts_two_of_continue_then_return_extraFuel extraFuel state state' state'
-- SORRY'D:               (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR]))
-- SORRY'D:               (YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]))
-- SORRY'D:               tailIR retVal hmstore hreturn)
-- SORRY'D:         have hirExec' :
-- SORRY'D:             execIRStmts (tailIR.length + 1 + 1 + extraFuel + 1)
-- SORRY'D:               state
-- SORRY'D:               (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR]) ::
-- SORRY'D:                 YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ::
-- SORRY'D:                 tailIR) =
-- SORRY'D:               .return retVal state' := by
-- SORRY'D:           simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hirExec
-- SORRY'D:         rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
-- SORRY'D:         dsimp [retVal, state']
-- SORRY'D:         constructor
-- SORRY'D:         · rw [hirExec']
-- SORRY'D:           simpa using (show
-- SORRY'D:             stmtResultMatchesIRExec fields
-- SORRY'D:               (SourceSemantics.StmtResult.return retVal runtime)
-- SORRY'D:               (.return retVal state') from ⟨rfl, hruntime'⟩)
-- SORRY'D:         · rw [hirExec']
-- SORRY'D:           simpa using (show
-- SORRY'D:             stmtResultMatchesIRExecExact
-- SORRY'D:               (SourceSemantics.StmtResult.return retVal runtime)
-- SORRY'D:               (.return retVal state') from ⟨hexact', hbounded⟩)
-- SORRY'D:   | stop hrest ih =>
-- SORRY'D:       rename_i scope rest
-- SORRY'D:       rcases ih (runtime := runtime) (state := state)
-- SORRY'D:           (inScopeNames := collectStmtNames (.stop) ++ inScopeNames)
-- SORRY'D:           hscope hexact hbounded hruntime with
-- SORRY'D:         ⟨tailIR, htailCompile, htailSem, htailExact⟩
-- SORRY'D:       refine ⟨[YulStmt.expr (YulExpr.call "stop" [])] ++ tailIR, ?_, ?_⟩
-- SORRY'D:       · simpa [CompilationModel.compileStmtList, CompilationModel.compileStmt, htailCompile]
-- SORRY'D:       · have hstmt :
-- SORRY'D:             execIRStmt (tailIR.length + extraFuel + 1) state
-- SORRY'D:               (YulStmt.expr (YulExpr.call "stop" [])) =
-- SORRY'D:               .stop state := by
-- SORRY'D:           simp [execIRStmt]
-- SORRY'D:         have hirExec :
-- SORRY'D:             execIRStmts (tailIR.length + extraFuel + 2) state
-- SORRY'D:               (YulStmt.expr (YulExpr.call "stop" []) :: tailIR) =
-- SORRY'D:               .stop state := by
-- SORRY'D:           simpa using
-- SORRY'D:             (execIRStmts_cons_of_execIRStmt_stop_extraFuel extraFuel state state
-- SORRY'D:               (YulStmt.expr (YulExpr.call "stop" [])) tailIR hstmt)
-- SORRY'D:         have hirExec' :
-- SORRY'D:             execIRStmts (tailIR.length + 1 + extraFuel + 1) state
-- SORRY'D:               (YulStmt.expr (YulExpr.call "stop" []) :: tailIR) =
-- SORRY'D:               .stop state := by
-- SORRY'D:           simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hirExec
-- SORRY'D:         rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
-- SORRY'D:         simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, hirExec'] using
-- SORRY'D:           (show stmtResultMatchesIRExec fields (SourceSemantics.StmtResult.stop runtime) (.stop state) ∧
-- SORRY'D:               stmtResultMatchesIRExecExact (SourceSemantics.StmtResult.stop runtime) (.stop state) from
-- SORRY'D:             ⟨hruntime, ⟨hexact, hbounded⟩⟩)

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
      intro next
      simp only [SourceSemantics.execStmtList, SourceSemantics.execStmt]
      cases SourceSemantics.evalExpr fields runtime _ <;> simp_all
  | assignVar hvalue hinScope hrest ih =>
      intro next
      simp only [SourceSemantics.execStmtList, SourceSemantics.execStmt]
      cases SourceSemantics.evalExpr fields runtime _ <;> simp_all
  | require_ hcond hinScope hrest ih =>
      intro next
      simp only [SourceSemantics.execStmtList, SourceSemantics.execStmt]
      cases heval : SourceSemantics.evalExpr fields runtime _ with
      | none => simp
      | some resolved =>
          simp only [heval]
          by_cases hne : resolved != 0 <;> simp_all
  | return_ hvalue hinScope hrest =>
      intro next
      simp only [SourceSemantics.execStmtList, SourceSemantics.execStmt]
      cases SourceSemantics.evalExpr fields runtime _ <;> simp
  | stop hrest =>
      intro next
      simp [SourceSemantics.execStmtList, SourceSemantics.execStmt]
  | ite hcond hinScope hthen helse hrest ih_then ih_else =>
      intro next
      simp only [SourceSemantics.execStmtList, SourceSemantics.execStmt]
      cases heval : SourceSemantics.evalExpr fields runtime _ with
      | none => simp
      | some resolved =>
          simp only [heval]
          by_cases hne : resolved != 0
          · simp only [hne, ↓reduceIte, bne_self_eq_false, Bool.false_eq_true]
            have hbranch := ih_then (runtime := runtime)
            cases hexec : SourceSemantics.execStmtList fields runtime _ with
            | «continue» next' => exact absurd hexec (hbranch next')
            | stop _ | «return» _ _ | revert => simp [hexec]
          · simp only [hne, ↓reduceIte, bne_self_eq_false, Bool.false_eq_true]
            have hbranch := ih_else (runtime := runtime)
            cases hexec : SourceSemantics.execStmtList fields runtime _ with
            | «continue» next' => exact absurd hexec (hbranch next')
            | stop _ | «return» _ _ | revert => simp [hexec]

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
    {condValue : Nat}
    (hthen : StmtListTerminalCore scope thenBranch)
    (hcondEval : SourceSemantics.evalExpr fields runtime cond = some condValue)
    (hcondTrue : condValue != 0) :
    SourceSemantics.execStmtList fields runtime (.ite cond thenBranch elseBranch :: rest) =
      SourceSemantics.execStmtList fields runtime thenBranch := by
  simp only [SourceSemantics.execStmtList, SourceSemantics.execStmt, hcondEval, hcondTrue, ↓reduceIte]
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
    {condValue : Nat}
    (helse : StmtListTerminalCore scope elseBranch)
    (hcondEval : SourceSemantics.evalExpr fields runtime cond = some condValue)
    (hcondFalse : (condValue != 0) = false) :
    SourceSemantics.execStmtList fields runtime (.ite cond thenBranch elseBranch :: rest) =
      SourceSemantics.execStmtList fields runtime elseBranch := by
  simp only [SourceSemantics.execStmtList, SourceSemantics.execStmt, hcondEval, hcondFalse, ↓reduceIte]
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
    {sourceCondValue : Nat}
    {irExec : IRExecResult}
    (hthen : StmtListTerminalCore scope thenBranch)
    (hmatch :
      stmtResultMatchesIRExec fields
        (SourceSemantics.execStmtList fields runtime thenBranch)
        irExec)
    (hcondEval : SourceSemantics.evalExpr fields runtime cond = some sourceCondValue)
    (hcondTrue : sourceCondValue != 0)
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
      (condValue := sourceCondValue)
      hthen
      hcondEval
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

-- TYPESIG_SORRY: theorem stmtResultMatchesIRExec_compiled_terminal_ite_then
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {runtime : SourceSemantics.RuntimeState}
-- TYPESIG_SORRY:     {state : IRState}
-- TYPESIG_SORRY:     {scope : List String}
-- TYPESIG_SORRY:     {cond : Expr}
-- TYPESIG_SORRY:     {thenBranch elseBranch rest : List Stmt}
-- TYPESIG_SORRY:     {extraFuel : Nat}
-- TYPESIG_SORRY:     {tempName : String}
-- TYPESIG_SORRY:     {condIR : YulExpr}
-- TYPESIG_SORRY:     {thenIR elseIR tailIR : List YulStmt}
-- TYPESIG_SORRY:     {condValue : Nat}
-- TYPESIG_SORRY:     {irExec : IRExecResult}
-- TYPESIG_SORRY:     (hthen : StmtListTerminalCore scope thenBranch)
-- TYPESIG_SORRY:     (hmatch :
-- TYPESIG_SORRY:       stmtResultMatchesIRExec fields
-- TYPESIG_SORRY:         (SourceSemantics.execStmtList fields runtime thenBranch)
-- TYPESIG_SORRY:         irExec)
-- TYPESIG_SORRY:     (hcondTrue : (SourceSemantics.evalExpr fields runtime cond != 0) = true)
-- TYPESIG_SORRY:     (hcond : evalIRExpr state condIR = some condValue)
-- TYPESIG_SORRY:     (hcondNonzero : condValue ≠ 0)
-- TYPESIG_SORRY:     (hthenExec :
-- TYPESIG_SORRY:       execIRStmts
-- TYPESIG_SORRY:         (sizeOf thenIR +
-- TYPESIG_SORRY:           (sizeOf
-- TYPESIG_SORRY:               ([YulStmt.block
-- TYPESIG_SORRY:                   [ YulStmt.let_ tempName condIR
-- TYPESIG_SORRY:                   , YulStmt.if_ (YulExpr.ident tempName) thenIR
-- TYPESIG_SORRY:                   , YulStmt.if_
-- TYPESIG_SORRY:                       (YulExpr.call "iszero" [YulExpr.ident tempName])
-- TYPESIG_SORRY:                       elseIR
-- TYPESIG_SORRY:                   ]] ++ tailIR) -
-- TYPESIG_SORRY:             (sizeOf thenIR + 5) +
-- TYPESIG_SORRY:             extraFuel) + 1)
-- TYPESIG_SORRY:         (state.setVar tempName condValue) thenIR = irExec) :
-- TYPESIG_SORRY:     stmtResultMatchesIRExec fields
-- TYPESIG_SORRY:       (SourceSemantics.execStmtList fields runtime (.ite cond thenBranch elseBranch :: rest))
-- TYPESIG_SORRY:       (execIRStmts
-- TYPESIG_SORRY:         (sizeOf
-- TYPESIG_SORRY:             ([YulStmt.block
-- TYPESIG_SORRY:                 [ YulStmt.let_ tempName condIR
-- TYPESIG_SORRY:                 , YulStmt.if_ (YulExpr.ident tempName) thenIR
-- TYPESIG_SORRY:                 , YulStmt.if_
-- TYPESIG_SORRY:                     (YulExpr.call "iszero" [YulExpr.ident tempName])
-- TYPESIG_SORRY:                     elseIR
-- TYPESIG_SORRY:                 ]] ++ tailIR) + extraFuel + 1)
-- TYPESIG_SORRY:         state
-- TYPESIG_SORRY:         ([YulStmt.block
-- TYPESIG_SORRY:             [ YulStmt.let_ tempName condIR
-- TYPESIG_SORRY:             , YulStmt.if_ (YulExpr.ident tempName) thenIR
-- TYPESIG_SORRY:             , YulStmt.if_
-- TYPESIG_SORRY:                 (YulExpr.call "iszero" [YulExpr.ident tempName])
-- TYPESIG_SORRY:                 elseIR
-- TYPESIG_SORRY:             ]] ++ tailIR)) := by sorry
-- SORRY'D:   have hirNoContinue :
-- SORRY'D:       ∀ next, irExec ≠ .continue next := by
-- SORRY'D:     exact stmtResultMatchesIRExec_ir_not_continue_of_terminal_core
-- SORRY'D:       (fields := fields)
-- SORRY'D:       (runtime := runtime)
-- SORRY'D:       (scope := scope)
-- SORRY'D:       (stmts := thenBranch)
-- SORRY'D:       (irExec := irExec)
-- SORRY'D:       hthen
-- SORRY'D:       hmatch
-- SORRY'D:   have hsourceEq :
-- SORRY'D:       SourceSemantics.execStmtList fields runtime (.ite cond thenBranch elseBranch :: rest) =
-- SORRY'D:         SourceSemantics.execStmtList fields runtime thenBranch :=
-- SORRY'D:     execStmtList_terminal_core_ite_then_eq
-- SORRY'D:       (fields := fields)
-- SORRY'D:       (runtime := runtime)
-- SORRY'D:       (scope := scope)
-- SORRY'D:       (cond := cond)
-- SORRY'D:       (thenBranch := thenBranch)
-- SORRY'D:       (elseBranch := elseBranch)
-- SORRY'D:       (rest := rest)
-- SORRY'D:       hthen
-- SORRY'D:       hcondTrue
-- SORRY'D:   have hirEq :
-- SORRY'D:       execIRStmts
-- SORRY'D:         (sizeOf
-- SORRY'D:             ([YulStmt.block
-- SORRY'D:                 [ YulStmt.let_ tempName condIR
-- SORRY'D:                 , YulStmt.if_ (YulExpr.ident tempName) thenIR
-- SORRY'D:                 , YulStmt.if_
-- SORRY'D:                     (YulExpr.call "iszero" [YulExpr.ident tempName])
-- SORRY'D:                     elseIR
-- SORRY'D:                 ]] ++ tailIR) + extraFuel + 1)
-- SORRY'D:         state
-- SORRY'D:         ([YulStmt.block
-- SORRY'D:             [ YulStmt.let_ tempName condIR
-- SORRY'D:             , YulStmt.if_ (YulExpr.ident tempName) thenIR
-- SORRY'D:             , YulStmt.if_
-- SORRY'D:                 (YulExpr.call "iszero" [YulExpr.ident tempName])
-- SORRY'D:                 elseIR
-- SORRY'D:             ]] ++ tailIR) =
-- SORRY'D:       irExec :=
-- SORRY'D:     execIRStmts_compiled_terminal_ite_then_of_irExec
-- SORRY'D:       extraFuel state tempName condIR thenIR elseIR tailIR condValue irExec
-- SORRY'D:       hcond hcondNonzero hthenExec hirNoContinue
-- SORRY'D:   rw [hsourceEq, hirEq]
-- SORRY'D:   exact hmatch

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
    {sourceCondValue : Nat}
    {irExec : IRExecResult}
    (helse : StmtListTerminalCore scope elseBranch)
    (hmatch :
      stmtResultMatchesIRExec fields
        (SourceSemantics.execStmtList fields runtime elseBranch)
        irExec)
    (hcondEval : SourceSemantics.evalExpr fields runtime cond = some sourceCondValue)
    (hcondFalse : (sourceCondValue != 0) = false)
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
      (condValue := sourceCondValue)
      helse
      hcondEval
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

-- TYPESIG_SORRY: theorem stmtResultMatchesIRExec_compiled_terminal_ite_else
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {runtime : SourceSemantics.RuntimeState}
-- TYPESIG_SORRY:     {state : IRState}
-- TYPESIG_SORRY:     {scope : List String}
-- TYPESIG_SORRY:     {cond : Expr}
-- TYPESIG_SORRY:     {thenBranch elseBranch rest : List Stmt}
-- TYPESIG_SORRY:     {extraFuel : Nat}
-- TYPESIG_SORRY:     {tempName : String}
-- TYPESIG_SORRY:     {condIR : YulExpr}
-- TYPESIG_SORRY:     {thenIR elseIR tailIR : List YulStmt}
-- TYPESIG_SORRY:     {condValue : Nat}
-- TYPESIG_SORRY:     {irExec : IRExecResult}
-- TYPESIG_SORRY:     (helse : StmtListTerminalCore scope elseBranch)
-- TYPESIG_SORRY:     (hmatch :
-- TYPESIG_SORRY:       stmtResultMatchesIRExec fields
-- TYPESIG_SORRY:         (SourceSemantics.execStmtList fields runtime elseBranch)
-- TYPESIG_SORRY:         irExec)
-- TYPESIG_SORRY:     (hcondFalse : (SourceSemantics.evalExpr fields runtime cond != 0) = false)
-- TYPESIG_SORRY:     (hcond : evalIRExpr state condIR = some condValue)
-- TYPESIG_SORRY:     (hcondZero : condValue = 0)
-- TYPESIG_SORRY:     (helseExec :
-- TYPESIG_SORRY:       execIRStmts
-- TYPESIG_SORRY:         (sizeOf elseIR +
-- TYPESIG_SORRY:           (sizeOf
-- TYPESIG_SORRY:               ([YulStmt.block
-- TYPESIG_SORRY:                   [ YulStmt.let_ tempName condIR
-- TYPESIG_SORRY:                   , YulStmt.if_ (YulExpr.ident tempName) thenIR
-- TYPESIG_SORRY:                   , YulStmt.if_
-- TYPESIG_SORRY:                       (YulExpr.call "iszero" [YulExpr.ident tempName])
-- TYPESIG_SORRY:                       elseIR
-- TYPESIG_SORRY:                   ]] ++ tailIR) -
-- TYPESIG_SORRY:             (sizeOf elseIR + 5) +
-- TYPESIG_SORRY:             extraFuel))
-- TYPESIG_SORRY:         (state.setVar tempName condValue) elseIR = irExec) :
-- TYPESIG_SORRY:     stmtResultMatchesIRExec fields
-- TYPESIG_SORRY:       (SourceSemantics.execStmtList fields runtime (.ite cond thenBranch elseBranch :: rest))
-- TYPESIG_SORRY:       (execIRStmts
-- TYPESIG_SORRY:         (sizeOf
-- TYPESIG_SORRY:             ([YulStmt.block
-- TYPESIG_SORRY:                 [ YulStmt.let_ tempName condIR
-- TYPESIG_SORRY:                 , YulStmt.if_ (YulExpr.ident tempName) thenIR
-- TYPESIG_SORRY:                 , YulStmt.if_
-- TYPESIG_SORRY:                     (YulExpr.call "iszero" [YulExpr.ident tempName])
-- TYPESIG_SORRY:                     elseIR
-- TYPESIG_SORRY:                 ]] ++ tailIR) + extraFuel + 1)
-- TYPESIG_SORRY:         state
-- TYPESIG_SORRY:         ([YulStmt.block
-- TYPESIG_SORRY:             [ YulStmt.let_ tempName condIR
-- TYPESIG_SORRY:             , YulStmt.if_ (YulExpr.ident tempName) thenIR
-- TYPESIG_SORRY:             , YulStmt.if_
-- TYPESIG_SORRY:                 (YulExpr.call "iszero" [YulExpr.ident tempName])
-- TYPESIG_SORRY:                 elseIR
-- TYPESIG_SORRY:             ]] ++ tailIR)) := by sorry
-- SORRY'D:   have hirNoContinue :
-- SORRY'D:       ∀ next, irExec ≠ .continue next := by
-- SORRY'D:     exact stmtResultMatchesIRExec_ir_not_continue_of_terminal_core
-- SORRY'D:       (fields := fields)
-- SORRY'D:       (runtime := runtime)
-- SORRY'D:       (scope := scope)
-- SORRY'D:       (stmts := elseBranch)
-- SORRY'D:       (irExec := irExec)
-- SORRY'D:       helse
-- SORRY'D:       hmatch
-- SORRY'D:   have hsourceEq :
-- SORRY'D:       SourceSemantics.execStmtList fields runtime (.ite cond thenBranch elseBranch :: rest) =
-- SORRY'D:         SourceSemantics.execStmtList fields runtime elseBranch :=
-- SORRY'D:     execStmtList_terminal_core_ite_else_eq
-- SORRY'D:       (fields := fields)
-- SORRY'D:       (runtime := runtime)
-- SORRY'D:       (scope := scope)
-- SORRY'D:       (cond := cond)
-- SORRY'D:       (thenBranch := thenBranch)
-- SORRY'D:       (elseBranch := elseBranch)
-- SORRY'D:       (rest := rest)
-- SORRY'D:       helse
-- SORRY'D:       hcondFalse
-- SORRY'D:   have hirEq :
-- SORRY'D:       execIRStmts
-- SORRY'D:         (sizeOf
-- SORRY'D:             ([YulStmt.block
-- SORRY'D:                 [ YulStmt.let_ tempName condIR
-- SORRY'D:                 , YulStmt.if_ (YulExpr.ident tempName) thenIR
-- SORRY'D:                 , YulStmt.if_
-- SORRY'D:                     (YulExpr.call "iszero" [YulExpr.ident tempName])
-- SORRY'D:                     elseIR
-- SORRY'D:                 ]] ++ tailIR) + extraFuel + 1)
-- SORRY'D:         state
-- SORRY'D:         ([YulStmt.block
-- SORRY'D:             [ YulStmt.let_ tempName condIR
-- SORRY'D:             , YulStmt.if_ (YulExpr.ident tempName) thenIR
-- SORRY'D:             , YulStmt.if_
-- SORRY'D:                 (YulExpr.call "iszero" [YulExpr.ident tempName])
-- SORRY'D:                 elseIR
-- SORRY'D:             ]] ++ tailIR) =
-- SORRY'D:       irExec :=
-- SORRY'D:     execIRStmts_compiled_terminal_ite_else_of_irExec
-- SORRY'D:       extraFuel state tempName condIR thenIR elseIR tailIR condValue irExec
-- SORRY'D:       hcond hcondZero helseExec hirNoContinue
-- SORRY'D:   rw [hsourceEq, hirEq]
-- SORRY'D:   exact hmatch

-- TYPESIG_SORRY: theorem execIRStmts_compiled_return_core_append_wholeFuel
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {runtime : SourceSemantics.RuntimeState}
-- TYPESIG_SORRY:     {state : IRState}
-- TYPESIG_SORRY:     {value : Expr}
-- TYPESIG_SORRY:     {tailIR : List YulStmt}
-- TYPESIG_SORRY:     {extraFuel : Nat}
-- TYPESIG_SORRY:     (hcore : ExprCompileCore value)
-- TYPESIG_SORRY:     (hexact : bindingsExactlyMatchIRVars runtime.bindings state)
-- TYPESIG_SORRY:     (hbounded : bindingsBounded runtime.bindings)
-- TYPESIG_SORRY:     (hpresent : exprBoundNamesPresent value runtime.bindings)
-- TYPESIG_SORRY:     (hruntime : runtimeStateMatchesIR fields runtime state) :
-- TYPESIG_SORRY:     let retVal := SourceSemantics.evalExpr fields runtime value
-- TYPESIG_SORRY:     let state' := { state with memory := fun o => if o = 0 then retVal else state.memory o }
-- TYPESIG_SORRY:     ∃ valueIR,
-- TYPESIG_SORRY:       CompilationModel.compileExpr fields .calldata value = Except.ok valueIR ∧
-- TYPESIG_SORRY:       execIRStmts
-- TYPESIG_SORRY:         (sizeOf
-- TYPESIG_SORRY:             ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
-- TYPESIG_SORRY:              , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
-- TYPESIG_SORRY:               tailIR) + extraFuel + 1)
-- TYPESIG_SORRY:         state
-- TYPESIG_SORRY:         ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
-- TYPESIG_SORRY:          , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
-- TYPESIG_SORRY:           tailIR) =
-- TYPESIG_SORRY:         .return retVal state' := by sorry
-- SORRY'D:   rcases compileExpr_core_ok (fields := fields) hcore with ⟨valueIR, hvalueIR⟩
-- SORRY'D:   let retVal := SourceSemantics.evalExpr fields runtime value
-- SORRY'D:   let state' := { state with memory := fun o => if o = 0 then retVal else state.memory o }
-- SORRY'D:   have heval := eval_compileExpr_core hcore hexact hbounded hpresent hruntime
-- SORRY'D:   rw [hvalueIR] at heval
-- SORRY'D:   have heval' : evalIRExpr state valueIR = some retVal := by
-- SORRY'D:     simpa [retVal] using heval
-- SORRY'D:   have hmstoreFuelNeZero :
-- SORRY'D:       sizeOf
-- SORRY'D:           ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
-- SORRY'D:            , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
-- SORRY'D:             tailIR) + extraFuel ≠ 0 := by
-- SORRY'D:     have hprefixLen :
-- SORRY'D:         2 ≤
-- SORRY'D:           ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
-- SORRY'D:            , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
-- SORRY'D:             tailIR).length := by
-- SORRY'D:       simp
-- SORRY'D:     have hlen :
-- SORRY'D:         ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
-- SORRY'D:          , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
-- SORRY'D:           tailIR).length ≤
-- SORRY'D:           sizeOf
-- SORRY'D:             ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
-- SORRY'D:              , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
-- SORRY'D:               tailIR) := by
-- SORRY'D:       exact yulStmtList_length_le_sizeOf _
-- SORRY'D:     omega
-- SORRY'D:   have hreturnFuelNeZero :
-- SORRY'D:       sizeOf
-- SORRY'D:           ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
-- SORRY'D:            , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
-- SORRY'D:             tailIR) + extraFuel - 1 ≠ 0 := by
-- SORRY'D:     have hprefixLen :
-- SORRY'D:         2 ≤
-- SORRY'D:           ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
-- SORRY'D:            , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
-- SORRY'D:             tailIR).length := by
-- SORRY'D:       simp
-- SORRY'D:     have hlen :
-- SORRY'D:         ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
-- SORRY'D:          , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
-- SORRY'D:           tailIR).length ≤
-- SORRY'D:           sizeOf
-- SORRY'D:             ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
-- SORRY'D:              , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
-- SORRY'D:               tailIR) := by
-- SORRY'D:       exact yulStmtList_length_le_sizeOf _
-- SORRY'D:     omega
-- SORRY'D:   have hmstore :
-- SORRY'D:       execIRStmt
-- SORRY'D:           (sizeOf
-- SORRY'D:               ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
-- SORRY'D:                , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
-- SORRY'D:                 tailIR) + extraFuel)
-- SORRY'D:           state
-- SORRY'D:           (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])) =
-- SORRY'D:         .continue state' := by
-- SORRY'D:     simpa [state'] using
-- SORRY'D:       execIRStmt_mstore_of_eval_nonzeroFuel
-- SORRY'D:         (fuel :=
-- SORRY'D:           sizeOf
-- SORRY'D:             ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
-- SORRY'D:              , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
-- SORRY'D:               tailIR) + extraFuel)
-- SORRY'D:         (state := state)
-- SORRY'D:         (offset := 0)
-- SORRY'D:         (valueExpr := valueIR)
-- SORRY'D:         (value := retVal)
-- SORRY'D:         hmstoreFuelNeZero
-- SORRY'D:         heval'
-- SORRY'D:   have hreturn :
-- SORRY'D:       execIRStmt
-- SORRY'D:           (sizeOf
-- SORRY'D:               ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
-- SORRY'D:                , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
-- SORRY'D:                 tailIR) + extraFuel - 1)
-- SORRY'D:           state'
-- SORRY'D:           (YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])) =
-- SORRY'D:         .return retVal state' := by
-- SORRY'D:     simpa [state', retVal] using
-- SORRY'D:       execIRStmt_return32_of_memory_nonzeroFuel
-- SORRY'D:         (fuel :=
-- SORRY'D:           sizeOf
-- SORRY'D:             ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
-- SORRY'D:              , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
-- SORRY'D:               tailIR) + extraFuel - 1)
-- SORRY'D:         (state := state')
-- SORRY'D:         (offset := 0)
-- SORRY'D:         hreturnFuelNeZero
-- SORRY'D:   refine ⟨valueIR, hvalueIR, ?_⟩
-- SORRY'D:   exact execIRStmts_two_append_of_continue_then_return_wholeFuel
-- SORRY'D:     (extraFuel := extraFuel)
-- SORRY'D:     (state := state)
-- SORRY'D:     (mid := state')
-- SORRY'D:     (next := state')
-- SORRY'D:     (stmt1 := YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR]))
-- SORRY'D:     (stmt2 := YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]))
-- SORRY'D:     (rest := tailIR)
-- SORRY'D:     (value := retVal)
-- SORRY'D:     hmstore
-- SORRY'D:     hreturn

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
    let retVal := (SourceSemantics.evalExpr fields runtime value).getD 0
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
  have heval := eval_compileExpr_core_of_scope hcore hexact hinScope hbounded hpresent hruntime
  rw [hvalueIR] at heval
  simp [Except.toOption] at heval
  rcases hIR : evalIRExpr state valueIR with _ | v
  · simp [hIR, Option.bind] at heval
  · simp [hIR, Option.bind] at heval
    have hEvalSrc : SourceSemantics.evalExpr fields runtime value = some v := heval.symm
    have hRetVal : (SourceSemantics.evalExpr fields runtime value).getD 0 = v := by
      rw [hEvalSrc]; rfl
    rw [hRetVal]
    set retVal := v
    set state' := { state with memory := fun o => if o = 0 then retVal else state.memory o }
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
          hIR
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
-- SORRY'D:   rcases compileExpr_core_ok (fields := fields) hcore with ⟨valueIR, hvalueIR⟩
-- SORRY'D:   let retVal := SourceSemantics.evalExpr fields runtime value
-- SORRY'D:   let state' := { state with memory := fun o => if o = 0 then retVal else state.memory o }
-- SORRY'D:   have heval :=
-- SORRY'D:     eval_compileExpr_core_of_scope hcore hexact hinScope hbounded hpresent hruntime
-- SORRY'D:   rw [hvalueIR] at heval
-- SORRY'D:   have heval' : evalIRExpr state valueIR = some retVal := by
-- SORRY'D:     simpa [retVal] using heval
-- SORRY'D:   have hmstoreFuelNeZero :
-- SORRY'D:       sizeOf
-- SORRY'D:           ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
-- SORRY'D:            , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
-- SORRY'D:             tailIR) + extraFuel ≠ 0 := by
-- SORRY'D:     have hprefixLen :
-- SORRY'D:         2 ≤
-- SORRY'D:           ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
-- SORRY'D:            , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
-- SORRY'D:             tailIR).length := by
-- SORRY'D:       simp
-- SORRY'D:     have hlen :
-- SORRY'D:         ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
-- SORRY'D:          , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
-- SORRY'D:           tailIR).length ≤
-- SORRY'D:           sizeOf
-- SORRY'D:             ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
-- SORRY'D:              , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
-- SORRY'D:               tailIR) := by
-- SORRY'D:       exact yulStmtList_length_le_sizeOf _
-- SORRY'D:     omega
-- SORRY'D:   have hreturnFuelNeZero :
-- SORRY'D:       sizeOf
-- SORRY'D:           ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
-- SORRY'D:            , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
-- SORRY'D:             tailIR) + extraFuel - 1 ≠ 0 := by
-- SORRY'D:     have hprefixLen :
-- SORRY'D:         2 ≤
-- SORRY'D:           ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
-- SORRY'D:            , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
-- SORRY'D:             tailIR).length := by
-- SORRY'D:       simp
-- SORRY'D:     have hlen :
-- SORRY'D:         ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
-- SORRY'D:          , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
-- SORRY'D:           tailIR).length ≤
-- SORRY'D:           sizeOf
-- SORRY'D:             ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
-- SORRY'D:              , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
-- SORRY'D:               tailIR) := by
-- SORRY'D:       exact yulStmtList_length_le_sizeOf _
-- SORRY'D:     omega
-- SORRY'D:   have hmstore :
-- SORRY'D:       execIRStmt
-- SORRY'D:           (sizeOf
-- SORRY'D:               ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
-- SORRY'D:                , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
-- SORRY'D:                 tailIR) + extraFuel)
-- SORRY'D:           state
-- SORRY'D:           (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])) =
-- SORRY'D:         .continue state' := by
-- SORRY'D:     simpa [state'] using
-- SORRY'D:       execIRStmt_mstore_of_eval_nonzeroFuel
-- SORRY'D:         (fuel :=
-- SORRY'D:           sizeOf
-- SORRY'D:             ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
-- SORRY'D:              , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
-- SORRY'D:               tailIR) + extraFuel)
-- SORRY'D:         (state := state)
-- SORRY'D:         (offset := 0)
-- SORRY'D:         (valueExpr := valueIR)
-- SORRY'D:         (value := retVal)
-- SORRY'D:         hmstoreFuelNeZero
-- SORRY'D:         heval'
-- SORRY'D:   have hreturn :
-- SORRY'D:       execIRStmt
-- SORRY'D:           (sizeOf
-- SORRY'D:               ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
-- SORRY'D:                , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
-- SORRY'D:                 tailIR) + extraFuel - 1)
-- SORRY'D:           state'
-- SORRY'D:           (YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])) =
-- SORRY'D:         .return retVal state' := by
-- SORRY'D:     simpa [state', retVal] using
-- SORRY'D:       execIRStmt_return32_of_memory_nonzeroFuel
-- SORRY'D:         (fuel :=
-- SORRY'D:           sizeOf
-- SORRY'D:             ([ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
-- SORRY'D:              , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++
-- SORRY'D:               tailIR) + extraFuel - 1)
-- SORRY'D:         (state := state')
-- SORRY'D:         (offset := 0)
-- SORRY'D:         hreturnFuelNeZero
-- SORRY'D:   refine ⟨valueIR, hvalueIR, ?_⟩
-- SORRY'D:   exact execIRStmts_two_append_of_continue_then_return_wholeFuel
-- SORRY'D:     (extraFuel := extraFuel)
-- SORRY'D:     (state := state)
-- SORRY'D:     (mid := state')
-- SORRY'D:     (next := state')
-- SORRY'D:     (stmt1 := YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR]))
-- SORRY'D:     (stmt2 := YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]))
-- SORRY'D:     (rest := tailIR)
-- SORRY'D:     (value := retVal)
-- SORRY'D:     hmstore
-- SORRY'D:     hreturn

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
    {valueNat : Nat}
    (hcore : ExprCompileCore value)
    (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hinScope : exprBoundNamesInScope value scope)
    (hscope : scopeNamesPresent scope runtime.bindings)
    (hbounded : bindingsBounded runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state)
    (hValueEval : SourceSemantics.evalExpr fields runtime value = some valueNat) :
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
  let runtime' :=
    { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
  let state' := state.setVar name valueNat
  have heval :=
    eval_compileExpr_core_of_scope hcore hexact hinScope hbounded hpresent hruntime
  rw [hvalueIR] at heval
  simp only [Except.toOption] at heval
  have heval' : evalIRExpr state valueIR = some valueNat := by
    rcases hIR : evalIRExpr state valueIR with _ | v
    · simp [hIR, Option.bind] at heval
    · simp [hIR, Option.bind] at heval
      rw [hValueEval] at heval
      simpa using heval
  have hvalueLt :=
    evalExpr_lt_evmModulus_core_of_scope hcore hexact hinScope hbounded hpresent hruntime
  rw [hValueEval] at hvalueLt; simp at hvalueLt
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

-- TYPESIG_SORRY: theorem execIRStmts_compiled_let_core_tailExtraFuel_of_scope
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {runtime : SourceSemantics.RuntimeState}
-- TYPESIG_SORRY:     {state : IRState}
-- TYPESIG_SORRY:     {scope : List String}
-- TYPESIG_SORRY:     {name : String}
-- TYPESIG_SORRY:     {value : Expr}
-- TYPESIG_SORRY:     {valueIR : YulExpr}
-- TYPESIG_SORRY:     {tailIR : List YulStmt}
-- TYPESIG_SORRY:     {extraFuel : Nat}
-- TYPESIG_SORRY:     {irExec : IRExecResult}
-- TYPESIG_SORRY:     (hcore : ExprCompileCore value)
-- TYPESIG_SORRY:     (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR)
-- TYPESIG_SORRY:     (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
-- TYPESIG_SORRY:     (hinScope : exprBoundNamesInScope value scope)
-- TYPESIG_SORRY:     (hscope : scopeNamesPresent scope runtime.bindings)
-- TYPESIG_SORRY:     (hbounded : bindingsBounded runtime.bindings)
-- TYPESIG_SORRY:     (hruntime : runtimeStateMatchesIR fields runtime state)
-- TYPESIG_SORRY:     (htail :
-- TYPESIG_SORRY:       let valueNat := SourceSemantics.evalExpr fields runtime value
-- TYPESIG_SORRY:       execIRStmts
-- TYPESIG_SORRY:         (sizeOf tailIR +
-- TYPESIG_SORRY:           (sizeOf ([YulStmt.let_ name valueIR] ++ tailIR) -
-- TYPESIG_SORRY:             (sizeOf tailIR + 1) +
-- TYPESIG_SORRY:             extraFuel) + 1)
-- TYPESIG_SORRY:         (state.setVar name valueNat)
-- TYPESIG_SORRY:         tailIR = irExec) :
-- TYPESIG_SORRY:     let valueNat := SourceSemantics.evalExpr fields runtime value
-- TYPESIG_SORRY:     let runtime' :=
-- TYPESIG_SORRY:       { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
-- TYPESIG_SORRY:     let state' := state.setVar name valueNat
-- TYPESIG_SORRY:     execIRStmts
-- TYPESIG_SORRY:       (sizeOf ([YulStmt.let_ name valueIR] ++ tailIR) + extraFuel + 1)
-- TYPESIG_SORRY:       state
-- TYPESIG_SORRY:       ([YulStmt.let_ name valueIR] ++ tailIR) = irExec ∧
-- TYPESIG_SORRY:     runtimeStateMatchesIR fields runtime' state' ∧
-- TYPESIG_SORRY:     bindingsExactlyMatchIRVarsOnScope (name :: scope) runtime'.bindings state' ∧
-- TYPESIG_SORRY:     bindingsBounded runtime'.bindings ∧
-- TYPESIG_SORRY:     scopeNamesPresent (name :: scope) runtime'.bindings := by sorry
-- SORRY'D:   rcases execIRStmts_compiled_let_core_append_wholeFuel_of_scope
-- SORRY'D:       (fields := fields)
-- SORRY'D:       (runtime := runtime)
-- SORRY'D:       (state := state)
-- SORRY'D:       (scope := scope)
-- SORRY'D:       (name := name)
-- SORRY'D:       (value := value)
-- SORRY'D:       (tailIR := tailIR)
-- SORRY'D:       (extraFuel := extraFuel)
-- SORRY'D:       hcore hexact hinScope hscope hbounded hruntime with
-- SORRY'D:     ⟨valueIR', hvalueIR', hwhole, hruntime', hexact', hbounded', hscope'⟩
-- SORRY'D:   rw [hvalueIR] at hvalueIR'
-- SORRY'D:   injection hvalueIR' with hEq
-- SORRY'D:   subst hEq
-- SORRY'D:   let valueNat := SourceSemantics.evalExpr fields runtime value
-- SORRY'D:   let runtime' :=
-- SORRY'D:     { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
-- SORRY'D:   let state' := state.setVar name valueNat
-- SORRY'D:   refine ⟨?_, hruntime', hexact', hbounded', hscope'⟩
-- SORRY'D:   exact execIRStmts_singleton_append_of_execIRStmt_continue_tailExtraFuel
-- SORRY'D:       (extraFuel := extraFuel)
-- SORRY'D:       (state := state)
-- SORRY'D:       (next := state')
-- SORRY'D:       (stmt := YulStmt.let_ name valueIR)
-- SORRY'D:       (rest := tailIR)
-- SORRY'D:       (irExec := irExec)
-- SORRY'D:       (by
-- SORRY'D:         have hpresent : exprBoundNamesPresent value runtime.bindings :=
-- SORRY'D:           exprBoundNamesPresent_of_scope hscope hinScope
-- SORRY'D:         have heval :=
-- SORRY'D:           eval_compileExpr_core_of_scope hcore hexact hinScope hbounded hpresent hruntime
-- SORRY'D:         rw [hvalueIR] at heval
-- SORRY'D:         have heval' : evalIRExpr state valueIR = some valueNat := by
-- SORRY'D:           simpa [valueNat] using heval
-- SORRY'D:         exact execIRStmt_let_of_eval_nonzeroFuel
-- SORRY'D:           (fuel := sizeOf ([YulStmt.let_ name valueIR] ++ tailIR) + extraFuel)
-- SORRY'D:           (state := state)
-- SORRY'D:           (name := name)
-- SORRY'D:           (valueExpr := valueIR)
-- SORRY'D:           (value := valueNat)
-- SORRY'D:           (sizeOf_singleton_append_extraFuel_ne_zero
-- SORRY'D:             (stmt := YulStmt.let_ name valueIR)
-- SORRY'D:             (tailIR := tailIR)
-- SORRY'D:             (extraFuel := extraFuel))
-- SORRY'D:           heval')
-- SORRY'D:       htail

theorem execIRStmts_compiled_assign_core_append_wholeFuel_of_scope
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope : List String}
    {name : String}
    {value : Expr}
    {tailIR : List YulStmt}
    {extraFuel : Nat}
    {valueNat : Nat}
    (hcore : ExprCompileCore value)
    (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hinScope : exprBoundNamesInScope value scope)
    (hscope : scopeNamesPresent scope runtime.bindings)
    (hbounded : bindingsBounded runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state)
    (hValueEval : SourceSemantics.evalExpr fields runtime value = some valueNat) :
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
  let runtime' :=
    { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
  let state' := state.setVar name valueNat
  have heval :=
    eval_compileExpr_core_of_scope hcore hexact hinScope hbounded hpresent hruntime
  rw [hvalueIR] at heval; simp only [Except.toOption] at heval
  have heval' : evalIRExpr state valueIR = some valueNat := by
    rcases hIR : evalIRExpr state valueIR with _ | v
    · simp [hIR, Option.bind] at heval
    · simp [hIR, Option.bind] at heval
      rw [hValueEval] at heval
      simpa using heval
  have hvalueLt :=
    evalExpr_lt_evmModulus_core_of_scope hcore hexact hinScope hbounded hpresent hruntime
  rw [hValueEval] at hvalueLt; simp at hvalueLt
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

-- TYPESIG_SORRY: theorem execIRStmts_compiled_assign_core_tailExtraFuel_of_scope
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {runtime : SourceSemantics.RuntimeState}
-- TYPESIG_SORRY:     {state : IRState}
-- TYPESIG_SORRY:     {scope : List String}
-- TYPESIG_SORRY:     {name : String}
-- TYPESIG_SORRY:     {value : Expr}
-- TYPESIG_SORRY:     {valueIR : YulExpr}
-- TYPESIG_SORRY:     {tailIR : List YulStmt}
-- TYPESIG_SORRY:     {extraFuel : Nat}
-- TYPESIG_SORRY:     {irExec : IRExecResult}
-- TYPESIG_SORRY:     (hcore : ExprCompileCore value)
-- TYPESIG_SORRY:     (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR)
-- TYPESIG_SORRY:     (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
-- TYPESIG_SORRY:     (hinScope : exprBoundNamesInScope value scope)
-- TYPESIG_SORRY:     (hscope : scopeNamesPresent scope runtime.bindings)
-- TYPESIG_SORRY:     (hbounded : bindingsBounded runtime.bindings)
-- TYPESIG_SORRY:     (hruntime : runtimeStateMatchesIR fields runtime state)
-- TYPESIG_SORRY:     (htail :
-- TYPESIG_SORRY:       let valueNat := SourceSemantics.evalExpr fields runtime value
-- TYPESIG_SORRY:       execIRStmts
-- TYPESIG_SORRY:         (sizeOf tailIR +
-- TYPESIG_SORRY:           (sizeOf ([YulStmt.assign name valueIR] ++ tailIR) -
-- TYPESIG_SORRY:             (sizeOf tailIR + 1) +
-- TYPESIG_SORRY:             extraFuel) + 1)
-- TYPESIG_SORRY:         (state.setVar name valueNat)
-- TYPESIG_SORRY:         tailIR = irExec) :
-- TYPESIG_SORRY:     let valueNat := SourceSemantics.evalExpr fields runtime value
-- TYPESIG_SORRY:     let runtime' :=
-- TYPESIG_SORRY:       { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
-- TYPESIG_SORRY:     let state' := state.setVar name valueNat
-- TYPESIG_SORRY:     execIRStmts
-- TYPESIG_SORRY:       (sizeOf ([YulStmt.assign name valueIR] ++ tailIR) + extraFuel + 1)
-- TYPESIG_SORRY:       state
-- TYPESIG_SORRY:       ([YulStmt.assign name valueIR] ++ tailIR) = irExec ∧
-- TYPESIG_SORRY:     runtimeStateMatchesIR fields runtime' state' ∧
-- TYPESIG_SORRY:     bindingsExactlyMatchIRVarsOnScope (name :: scope) runtime'.bindings state' ∧
-- TYPESIG_SORRY:     bindingsBounded runtime'.bindings ∧
-- TYPESIG_SORRY:     scopeNamesPresent (name :: scope) runtime'.bindings := by sorry
-- SORRY'D:   rcases execIRStmts_compiled_assign_core_append_wholeFuel_of_scope
-- SORRY'D:       (fields := fields)
-- SORRY'D:       (runtime := runtime)
-- SORRY'D:       (state := state)
-- SORRY'D:       (scope := scope)
-- SORRY'D:       (name := name)
-- SORRY'D:       (value := value)
-- SORRY'D:       (tailIR := tailIR)
-- SORRY'D:       (extraFuel := extraFuel)
-- SORRY'D:       hcore hexact hinScope hscope hbounded hruntime with
-- SORRY'D:     ⟨valueIR', hvalueIR', hwhole, hruntime', hexact', hbounded', hscope'⟩
-- SORRY'D:   rw [hvalueIR] at hvalueIR'
-- SORRY'D:   injection hvalueIR' with hEq
-- SORRY'D:   subst hEq
-- SORRY'D:   let valueNat := SourceSemantics.evalExpr fields runtime value
-- SORRY'D:   let runtime' :=
-- SORRY'D:     { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
-- SORRY'D:   let state' := state.setVar name valueNat
-- SORRY'D:   refine ⟨?_, hruntime', hexact', hbounded', hscope'⟩
-- SORRY'D:   exact execIRStmts_singleton_append_of_execIRStmt_continue_tailExtraFuel
-- SORRY'D:       (extraFuel := extraFuel)
-- SORRY'D:       (state := state)
-- SORRY'D:       (next := state')
-- SORRY'D:       (stmt := YulStmt.assign name valueIR)
-- SORRY'D:       (rest := tailIR)
-- SORRY'D:       (irExec := irExec)
-- SORRY'D:       (by
-- SORRY'D:         have hpresent : exprBoundNamesPresent value runtime.bindings :=
-- SORRY'D:           exprBoundNamesPresent_of_scope hscope hinScope
-- SORRY'D:         have heval :=
-- SORRY'D:           eval_compileExpr_core_of_scope hcore hexact hinScope hbounded hpresent hruntime
-- SORRY'D:         rw [hvalueIR] at heval
-- SORRY'D:         have heval' : evalIRExpr state valueIR = some valueNat := by
-- SORRY'D:           simpa [valueNat] using heval
-- SORRY'D:         exact execIRStmt_assign_of_eval_nonzeroFuel
-- SORRY'D:           (fuel := sizeOf ([YulStmt.assign name valueIR] ++ tailIR) + extraFuel)
-- SORRY'D:           (state := state)
-- SORRY'D:           (name := name)
-- SORRY'D:           (valueExpr := valueIR)
-- SORRY'D:           (value := valueNat)
-- SORRY'D:           (sizeOf_singleton_append_extraFuel_ne_zero
-- SORRY'D:             (stmt := YulStmt.assign name valueIR)
-- SORRY'D:             (tailIR := tailIR)
-- SORRY'D:             (extraFuel := extraFuel))
-- SORRY'D:           heval')
-- SORRY'D:       htail

theorem execIRStmts_compiled_require_core_pass_append_wholeFuel_of_scope
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope : List String}
    {cond : Expr}
    {message : String}
    {tailIR : List YulStmt}
    {extraFuel : Nat}
    {condValue : Nat}
    (hcore : ExprCompileCore cond)
    (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hinScope : exprBoundNamesInScope cond scope)
    (hscope : scopeNamesPresent scope runtime.bindings)
    (hbounded : bindingsBounded runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state)
    (hcondEval : SourceSemantics.evalExpr fields runtime cond = some condValue)
    (hcondNeZero : condValue ≠ 0) :
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
    have hdecideFalse : decide (SourceSemantics.evalExpr fields runtime cond = some 0) = false := by
      simp [hcondEval, hcondNeZero]
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
      hfailEval'
      rfl
  refine ⟨failCond, hfailCompile, ?_⟩
  exact execIRStmts_singleton_append_of_execIRStmt_continue_wholeFuel
    (extraFuel := extraFuel)
    (state := state)
    (next := state)
    (stmt := YulStmt.if_ failCond (CompilationModel.revertWithMessage message))
    (rest := tailIR)
    hstmt

-- TYPESIG_SORRY: theorem execIRStmts_compiled_require_core_pass_tailExtraFuel_of_scope
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {runtime : SourceSemantics.RuntimeState}
-- TYPESIG_SORRY:     {state : IRState}
-- TYPESIG_SORRY:     {scope : List String}
-- TYPESIG_SORRY:     {cond : Expr}
-- TYPESIG_SORRY:     {message : String}
-- TYPESIG_SORRY:     {failCond : YulExpr}
-- TYPESIG_SORRY:     {tailIR : List YulStmt}
-- TYPESIG_SORRY:     {extraFuel : Nat}
-- TYPESIG_SORRY:     {irExec : IRExecResult}
-- TYPESIG_SORRY:     (hcore : ExprCompileCore cond)
-- TYPESIG_SORRY:     (hfailCompile : CompilationModel.compileRequireFailCond fields .calldata cond = Except.ok failCond)
-- TYPESIG_SORRY:     (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
-- TYPESIG_SORRY:     (hinScope : exprBoundNamesInScope cond scope)
-- TYPESIG_SORRY:     (hscope : scopeNamesPresent scope runtime.bindings)
-- TYPESIG_SORRY:     (hbounded : bindingsBounded runtime.bindings)
-- TYPESIG_SORRY:     (hruntime : runtimeStateMatchesIR fields runtime state)
-- TYPESIG_SORRY:     (hcondNeZero : SourceSemantics.evalExpr fields runtime cond ≠ 0)
-- TYPESIG_SORRY:     (htail :
-- TYPESIG_SORRY:       execIRStmts
-- TYPESIG_SORRY:         (sizeOf tailIR +
-- TYPESIG_SORRY:           (sizeOf
-- TYPESIG_SORRY:               ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) -
-- TYPESIG_SORRY:             (sizeOf tailIR + 1) +
-- TYPESIG_SORRY:             extraFuel) + 1)
-- TYPESIG_SORRY:         state
-- TYPESIG_SORRY:         tailIR = irExec) :
-- TYPESIG_SORRY:     execIRStmts
-- TYPESIG_SORRY:       (sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) + extraFuel + 1)
-- TYPESIG_SORRY:       state
-- TYPESIG_SORRY:       ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) = irExec := by sorry
-- SORRY'D:   rcases execIRStmts_compiled_require_core_pass_append_wholeFuel_of_scope
-- SORRY'D:       (fields := fields)
-- SORRY'D:       (runtime := runtime)
-- SORRY'D:       (state := state)
-- SORRY'D:       (scope := scope)
-- SORRY'D:       (cond := cond)
-- SORRY'D:       (message := message)
-- SORRY'D:       (tailIR := tailIR)
-- SORRY'D:       (extraFuel := extraFuel)
-- SORRY'D:       hcore hexact hinScope hscope hbounded hruntime hcondNeZero with
-- SORRY'D:     ⟨failCond', hfailCompile', hwhole⟩
-- SORRY'D:   rw [hfailCompile] at hfailCompile'
-- SORRY'D:   injection hfailCompile' with hEq
-- SORRY'D:   subst hEq
-- SORRY'D:   exact execIRStmts_singleton_append_of_execIRStmt_continue_tailExtraFuel
-- SORRY'D:     (extraFuel := extraFuel)
-- SORRY'D:     (state := state)
-- SORRY'D:     (next := state)
-- SORRY'D:     (stmt := YulStmt.if_ failCond (CompilationModel.revertWithMessage message))
-- SORRY'D:     (rest := tailIR)
-- SORRY'D:     (irExec := irExec)
-- SORRY'D:     (by
-- SORRY'D:       have hpresent : exprBoundNamesPresent cond runtime.bindings :=
-- SORRY'D:         exprBoundNamesPresent_of_scope hscope hinScope
-- SORRY'D:       rcases eval_compileRequireFailCond_core_of_scope
-- SORRY'D:           (fields := fields)
-- SORRY'D:           (runtime := runtime)
-- SORRY'D:           (state := state)
-- SORRY'D:           (scope := scope)
-- SORRY'D:           (cond := cond)
-- SORRY'D:           hcore hexact hinScope hbounded hpresent hruntime with
-- SORRY'D:         ⟨failCond', hfailCompile', hfailEval⟩
-- SORRY'D:       rw [hfailCompile] at hfailCompile'
-- SORRY'D:       injection hfailCompile' with hEq
-- SORRY'D:       subst hEq
-- SORRY'D:       exact execIRStmt_if_false_of_eval_nonzeroFuel
-- SORRY'D:         (fuel :=
-- SORRY'D:           sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) + extraFuel)
-- SORRY'D:         (state := state)
-- SORRY'D:         (cond := failCond)
-- SORRY'D:         (body := CompilationModel.revertWithMessage message)
-- SORRY'D:         (value := 0)
-- SORRY'D:         (sizeOf_singleton_append_extraFuel_ne_zero
-- SORRY'D:           (stmt := YulStmt.if_ failCond (CompilationModel.revertWithMessage message))
-- SORRY'D:           (tailIR := tailIR)
-- SORRY'D:           (extraFuel := extraFuel))
-- SORRY'D:         (by simpa [SourceSemantics.boolWord, hcondNeZero] using hfailEval)
-- SORRY'D:         rfl)
-- SORRY'D:     htail

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
    (hcondZero : SourceSemantics.evalExpr fields runtime cond = some 0) :
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

-- TYPESIG_SORRY: theorem stmtResultMatchesIRExec_compiled_let_core_tailExtraFuel_of_scope
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {runtime : SourceSemantics.RuntimeState}
-- TYPESIG_SORRY:     {state : IRState}
-- TYPESIG_SORRY:     {scope : List String}
-- TYPESIG_SORRY:     {name : String}
-- TYPESIG_SORRY:     {value : Expr}
-- TYPESIG_SORRY:     {valueIR : YulExpr}
-- TYPESIG_SORRY:     {rest : List Stmt}
-- TYPESIG_SORRY:     {tailIR : List YulStmt}
-- TYPESIG_SORRY:     {extraFuel : Nat}
-- TYPESIG_SORRY:     (hcore : ExprCompileCore value)
-- TYPESIG_SORRY:     (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR)
-- TYPESIG_SORRY:     (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
-- TYPESIG_SORRY:     (hinScope : exprBoundNamesInScope value scope)
-- TYPESIG_SORRY:     (hscope : scopeNamesPresent scope runtime.bindings)
-- TYPESIG_SORRY:     (hbounded : bindingsBounded runtime.bindings)
-- TYPESIG_SORRY:     (hruntime : runtimeStateMatchesIR fields runtime state)
-- TYPESIG_SORRY:     (htail :
-- TYPESIG_SORRY:       let valueNat := SourceSemantics.evalExpr fields runtime value
-- TYPESIG_SORRY:       let runtime' :=
-- TYPESIG_SORRY:         { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
-- TYPESIG_SORRY:       stmtResultMatchesIRExec
-- TYPESIG_SORRY:         fields
-- TYPESIG_SORRY:         (SourceSemantics.execStmtList fields runtime' rest)
-- TYPESIG_SORRY:         (execIRStmts
-- TYPESIG_SORRY:           (sizeOf tailIR +
-- TYPESIG_SORRY:             (sizeOf ([YulStmt.let_ name valueIR] ++ tailIR) -
-- TYPESIG_SORRY:               (sizeOf tailIR + 1) +
-- TYPESIG_SORRY:               extraFuel) + 1)
-- TYPESIG_SORRY:           (state.setVar name valueNat)
-- TYPESIG_SORRY:           tailIR)) :
-- TYPESIG_SORRY:     stmtResultMatchesIRExec
-- TYPESIG_SORRY:       fields
-- TYPESIG_SORRY:       (SourceSemantics.execStmtList fields runtime (.letVar name value :: rest))
-- TYPESIG_SORRY:       (execIRStmts
-- TYPESIG_SORRY:         (sizeOf ([YulStmt.let_ name valueIR] ++ tailIR) + extraFuel + 1)
-- TYPESIG_SORRY:         state
-- TYPESIG_SORRY:         ([YulStmt.let_ name valueIR] ++ tailIR)) := by sorry
-- SORRY'D:   let valueNat := SourceSemantics.evalExpr fields runtime value
-- SORRY'D:   let runtime' :=
-- SORRY'D:     { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
-- SORRY'D:   let state' := state.setVar name valueNat
-- SORRY'D:   rcases execIRStmts_compiled_let_core_tailExtraFuel_of_scope
-- SORRY'D:       (fields := fields)
-- SORRY'D:       (runtime := runtime)
-- SORRY'D:       (state := state)
-- SORRY'D:       (scope := scope)
-- SORRY'D:       (name := name)
-- SORRY'D:       (value := value)
-- SORRY'D:       (valueIR := valueIR)
-- SORRY'D:       (tailIR := tailIR)
-- SORRY'D:       (extraFuel := extraFuel)
-- SORRY'D:       (irExec :=
-- SORRY'D:         execIRStmts
-- SORRY'D:           (sizeOf tailIR +
-- SORRY'D:             (sizeOf ([YulStmt.let_ name valueIR] ++ tailIR) -
-- SORRY'D:               (sizeOf tailIR + 1) +
-- SORRY'D:               extraFuel) + 1)
-- SORRY'D:           state'
-- SORRY'D:           tailIR)
-- SORRY'D:       hcore hvalueIR hexact hinScope hscope hbounded hruntime rfl with
-- SORRY'D:     ⟨hwhole, hruntime', hexact', hbounded', hscope'⟩
-- SORRY'D:   have hwhole' :
-- SORRY'D:       execIRStmts
-- SORRY'D:         (1 + (1 + sizeOf name + sizeOf valueIR) + sizeOf tailIR + extraFuel + 1)
-- SORRY'D:         state
-- SORRY'D:         (YulStmt.let_ name valueIR :: tailIR) =
-- SORRY'D:       execIRStmts
-- SORRY'D:         (sizeOf tailIR +
-- SORRY'D:           (sizeOf ([YulStmt.let_ name valueIR] ++ tailIR) -
-- SORRY'D:             (sizeOf tailIR + 1) +
-- SORRY'D:             extraFuel) + 1)
-- SORRY'D:         state'
-- SORRY'D:         tailIR := by
-- SORRY'D:     simpa using hwhole
-- SORRY'D:   rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
-- SORRY'D:   dsimp [runtime', valueNat]
-- SORRY'D:   rw [hwhole']
-- SORRY'D:   exact htail

-- TYPESIG_SORRY: theorem stmtResultMatchesIRExec_compiled_assign_core_tailExtraFuel_of_scope
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {runtime : SourceSemantics.RuntimeState}
-- TYPESIG_SORRY:     {state : IRState}
-- TYPESIG_SORRY:     {scope : List String}
-- TYPESIG_SORRY:     {name : String}
-- TYPESIG_SORRY:     {value : Expr}
-- TYPESIG_SORRY:     {valueIR : YulExpr}
-- TYPESIG_SORRY:     {rest : List Stmt}
-- TYPESIG_SORRY:     {tailIR : List YulStmt}
-- TYPESIG_SORRY:     {extraFuel : Nat}
-- TYPESIG_SORRY:     (hcore : ExprCompileCore value)
-- TYPESIG_SORRY:     (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR)
-- TYPESIG_SORRY:     (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
-- TYPESIG_SORRY:     (hinScope : exprBoundNamesInScope value scope)
-- TYPESIG_SORRY:     (hscope : scopeNamesPresent scope runtime.bindings)
-- TYPESIG_SORRY:     (hbounded : bindingsBounded runtime.bindings)
-- TYPESIG_SORRY:     (hruntime : runtimeStateMatchesIR fields runtime state)
-- TYPESIG_SORRY:     (htail :
-- TYPESIG_SORRY:       let valueNat := SourceSemantics.evalExpr fields runtime value
-- TYPESIG_SORRY:       let runtime' :=
-- TYPESIG_SORRY:         { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
-- TYPESIG_SORRY:       stmtResultMatchesIRExec
-- TYPESIG_SORRY:         fields
-- TYPESIG_SORRY:         (SourceSemantics.execStmtList fields runtime' rest)
-- TYPESIG_SORRY:         (execIRStmts
-- TYPESIG_SORRY:           (sizeOf tailIR +
-- TYPESIG_SORRY:             (sizeOf ([YulStmt.assign name valueIR] ++ tailIR) -
-- TYPESIG_SORRY:               (sizeOf tailIR + 1) +
-- TYPESIG_SORRY:               extraFuel) + 1)
-- TYPESIG_SORRY:           (state.setVar name valueNat)
-- TYPESIG_SORRY:           tailIR)) :
-- TYPESIG_SORRY:     stmtResultMatchesIRExec
-- TYPESIG_SORRY:       fields
-- TYPESIG_SORRY:       (SourceSemantics.execStmtList fields runtime (.assignVar name value :: rest))
-- TYPESIG_SORRY:       (execIRStmts
-- TYPESIG_SORRY:         (sizeOf ([YulStmt.assign name valueIR] ++ tailIR) + extraFuel + 1)
-- TYPESIG_SORRY:         state
-- TYPESIG_SORRY:         ([YulStmt.assign name valueIR] ++ tailIR)) := by sorry
-- SORRY'D:   let valueNat := SourceSemantics.evalExpr fields runtime value
-- SORRY'D:   let runtime' :=
-- SORRY'D:     { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
-- SORRY'D:   let state' := state.setVar name valueNat
-- SORRY'D:   rcases execIRStmts_compiled_assign_core_tailExtraFuel_of_scope
-- SORRY'D:       (fields := fields)
-- SORRY'D:       (runtime := runtime)
-- SORRY'D:       (state := state)
-- SORRY'D:       (scope := scope)
-- SORRY'D:       (name := name)
-- SORRY'D:       (value := value)
-- SORRY'D:       (valueIR := valueIR)
-- SORRY'D:       (tailIR := tailIR)
-- SORRY'D:       (extraFuel := extraFuel)
-- SORRY'D:       (irExec :=
-- SORRY'D:         execIRStmts
-- SORRY'D:           (sizeOf tailIR +
-- SORRY'D:             (sizeOf ([YulStmt.assign name valueIR] ++ tailIR) -
-- SORRY'D:               (sizeOf tailIR + 1) +
-- SORRY'D:               extraFuel) + 1)
-- SORRY'D:           state'
-- SORRY'D:           tailIR)
-- SORRY'D:       hcore hvalueIR hexact hinScope hscope hbounded hruntime rfl with
-- SORRY'D:     ⟨hwhole, hruntime', hexact', hbounded', hscope'⟩
-- SORRY'D:   have hwhole' :
-- SORRY'D:       execIRStmts
-- SORRY'D:         (1 + (1 + sizeOf name + sizeOf valueIR) + sizeOf tailIR + extraFuel + 1)
-- SORRY'D:         state
-- SORRY'D:         (YulStmt.assign name valueIR :: tailIR) =
-- SORRY'D:       execIRStmts
-- SORRY'D:         (sizeOf tailIR +
-- SORRY'D:           (sizeOf ([YulStmt.assign name valueIR] ++ tailIR) -
-- SORRY'D:             (sizeOf tailIR + 1) +
-- SORRY'D:             extraFuel) + 1)
-- SORRY'D:         state'
-- SORRY'D:         tailIR := by
-- SORRY'D:     simpa using hwhole
-- SORRY'D:   rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
-- SORRY'D:   dsimp [runtime', valueNat]
-- SORRY'D:   rw [hwhole']
-- SORRY'D:   exact htail

-- TYPESIG_SORRY: theorem stmtResultMatchesIRExec_compiled_require_core_pass_tailExtraFuel_of_scope
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {runtime : SourceSemantics.RuntimeState}
-- TYPESIG_SORRY:     {state : IRState}
-- TYPESIG_SORRY:     {scope : List String}
-- TYPESIG_SORRY:     {cond : Expr}
-- TYPESIG_SORRY:     {message : String}
-- TYPESIG_SORRY:     {failCond : YulExpr}
-- TYPESIG_SORRY:     {rest : List Stmt}
-- TYPESIG_SORRY:     {tailIR : List YulStmt}
-- TYPESIG_SORRY:     {extraFuel : Nat}
-- TYPESIG_SORRY:     (hcore : ExprCompileCore cond)
-- TYPESIG_SORRY:     (hfailCompile : CompilationModel.compileRequireFailCond fields .calldata cond = Except.ok failCond)
-- TYPESIG_SORRY:     (hexact : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
-- TYPESIG_SORRY:     (hinScope : exprBoundNamesInScope cond scope)
-- TYPESIG_SORRY:     (hscope : scopeNamesPresent scope runtime.bindings)
-- TYPESIG_SORRY:     (hbounded : bindingsBounded runtime.bindings)
-- TYPESIG_SORRY:     (hruntime : runtimeStateMatchesIR fields runtime state)
-- TYPESIG_SORRY:     (hcondNeZero : SourceSemantics.evalExpr fields runtime cond ≠ 0)
-- TYPESIG_SORRY:     (htail :
-- TYPESIG_SORRY:       stmtResultMatchesIRExec
-- TYPESIG_SORRY:         fields
-- TYPESIG_SORRY:         (SourceSemantics.execStmtList fields runtime rest)
-- TYPESIG_SORRY:         (execIRStmts
-- TYPESIG_SORRY:           (sizeOf tailIR +
-- TYPESIG_SORRY:             (sizeOf
-- TYPESIG_SORRY:                 ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) -
-- TYPESIG_SORRY:               (sizeOf tailIR + 1) +
-- TYPESIG_SORRY:               extraFuel) + 1)
-- TYPESIG_SORRY:           state
-- TYPESIG_SORRY:           tailIR)) :
-- TYPESIG_SORRY:     stmtResultMatchesIRExec
-- TYPESIG_SORRY:       fields
-- TYPESIG_SORRY:       (SourceSemantics.execStmtList fields runtime (.require cond message :: rest))
-- TYPESIG_SORRY:       (execIRStmts
-- TYPESIG_SORRY:         (sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) +
-- TYPESIG_SORRY:           extraFuel + 1)
-- TYPESIG_SORRY:         state
-- TYPESIG_SORRY:         ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR)) := by sorry
-- SORRY'D:   have hwhole :=
-- SORRY'D:     execIRStmts_compiled_require_core_pass_tailExtraFuel_of_scope
-- SORRY'D:       (fields := fields)
-- SORRY'D:       (runtime := runtime)
-- SORRY'D:       (state := state)
-- SORRY'D:       (scope := scope)
-- SORRY'D:       (cond := cond)
-- SORRY'D:       (message := message)
-- SORRY'D:       (failCond := failCond)
-- SORRY'D:       (tailIR := tailIR)
-- SORRY'D:       (extraFuel := extraFuel)
-- SORRY'D:       (irExec :=
-- SORRY'D:         execIRStmts
-- SORRY'D:           (sizeOf tailIR +
-- SORRY'D:             (sizeOf
-- SORRY'D:                 ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) -
-- SORRY'D:               (sizeOf tailIR + 1) +
-- SORRY'D:               extraFuel) + 1)
-- SORRY'D:           state
-- SORRY'D:           tailIR)
-- SORRY'D:       hcore hfailCompile hexact hinScope hscope hbounded hruntime hcondNeZero rfl
-- SORRY'D:   have hcondTrue : (SourceSemantics.evalExpr fields runtime cond != 0) = true := by
-- SORRY'D:     simp [hcondNeZero]
-- SORRY'D:   rw [SourceSemantics.execStmtList, SourceSemantics.execStmt]
-- SORRY'D:   rw [hwhole]
-- SORRY'D:   simpa [hcondTrue] using htail

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
  -- Use the execution theorem to rewrite the IR side
  rcases execIRStmts_compiled_return_core_append_wholeFuel_of_scope
    hcore hexact hinScope hbounded (exprBoundNamesPresent_of_scope hscope hinScope) hruntime
    (tailIR := tailIR) (extraFuel := extraFuel) with ⟨valueIR', hvalueIR', hexec⟩
  -- valueIR' must equal valueIR
  rw [hvalueIR] at hvalueIR'
  cases hvalueIR'
  rw [hexec]
  -- Now reduce the source side
  simp only [SourceSemantics.execStmtList, SourceSemantics.execStmt]
  -- Get the evaluation bridge
  have heval := eval_compileExpr_core_of_scope hcore hexact hinScope hbounded
    (exprBoundNamesPresent_of_scope hscope hinScope) hruntime
  rw [hvalueIR] at heval
  simp [Except.toOption] at heval
  rcases hIR : evalIRExpr state valueIR with _ | v
  · simp [hIR, Option.bind] at heval
  · simp [hIR, Option.bind] at heval
    rw [show SourceSemantics.evalExpr fields runtime value = some v from heval.symm]
    -- Source = .return v runtime, IR = .return retVal state'
    -- retVal = (some v).getD 0 = v
    have hRetVal : (some v).getD 0 = v := rfl
    simp only [hRetVal, stmtResultMatchesIRExec]
    exact ⟨trivial, runtimeStateMatchesIR_setMemory hruntime 0 v⟩

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
  induction hterminal generalizing extraFuel runtime state inScopeNames with
  | letVar hvalue hinScope hrest ih =>
      rename_i scope name value rest
      have hpresent : exprBoundNamesPresent value runtime.bindings :=
        exprBoundNamesPresent_of_scope hscope hinScope
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      have heval := eval_compileExpr_core_of_scope hvalue hexact hinScope hbounded hpresent hruntime
      rw [hvalueIR] at heval; simp [Except.toOption] at heval
      rcases hIR : evalIRExpr state valueIR with _ | valueNat
      · simp [hIR, Option.bind] at heval
      · simp [hIR, Option.bind] at heval
        have hEvalSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
          heval.symm
        let runtime' :=
          { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
        let state' := state.setVar name valueNat
        have hvalueLt := evalExpr_lt_evmModulus_core_of_scope hvalue hexact hinScope hbounded hpresent hruntime
        rw [hEvalSrc] at hvalueLt; simp at hvalueLt
        have hruntime' : runtimeStateMatchesIR fields runtime' state' :=
          runtimeStateMatchesIR_setVar_bindValue hruntime name valueNat
        have hexact' : bindingsExactlyMatchIRVarsOnScope (name :: scope) runtime'.bindings state' :=
          bindingsExactlyMatchIRVarsOnScope_setVar_bindValue hexact
        have hbounded' : bindingsBounded runtime'.bindings :=
          bindingsBounded_bindValue hbounded name valueNat hvalueLt
        have hscope' : scopeNamesPresent (name :: scope) runtime'.bindings :=
          scopeNamesPresent_cons_bindValue hscope
        have hincluded' : scopeNamesIncluded (name :: scope)
            (collectStmtNames (.letVar name value) ++ inScopeNames) :=
          scopeNamesIncluded_collectStmtNames_letVar hincluded
        rcases ih (extraFuel + sizeOf (YulStmt.let_ name valueIR))
            (runtime := runtime') (state := state')
            (inScopeNames := collectStmtNames (.letVar name value) ++ inScopeNames)
            hincluded' hscope' hexact' hbounded' hruntime' with
          ⟨tailIR, htailCompile, htailSem⟩
        refine ⟨[YulStmt.let_ name valueIR] ++ tailIR, ?_, ?_⟩
        · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
          rw [hvalueIR]
          simp [htailCompile]
          exact rfl
        · have hstmt :
              execIRStmt (sizeOf ([YulStmt.let_ name valueIR] ++ tailIR) + extraFuel) state
                (YulStmt.let_ name valueIR) = .continue state' :=
            execIRStmt_let_of_eval_nonzeroFuel
              (sizeOf ([YulStmt.let_ name valueIR] ++ tailIR) + extraFuel) state name valueIR valueNat
              (sizeOf_singleton_append_extraFuel_ne_zero _ _ _)
              hIR
          have hirExec :=
            execIRStmts_singleton_append_of_execIRStmt_continue_wholeFuel
              extraFuel state state' (YulStmt.let_ name valueIR) tailIR hstmt
          -- hirExec : execIRStmts (sizeOf ([let_ ...] ++ tailIR) + extraFuel + 1) state ([let_ ...] ++ tailIR) =
          --   execIRStmts (sizeOf ([let_ ...] ++ tailIR) + extraFuel) state' tailIR
          -- htailSem has fuel sizeOf tailIR + (extraFuel + sizeOf (let_ ...)) + 1
          -- which equals sizeOf ([let_ ...] ++ tailIR) + extraFuel by List sizeOf arithmetic
          simp only [SourceSemantics.execStmtList, SourceSemantics.execStmt, hEvalSrc, hirExec]
          dsimp [runtime', state']
          convert htailSem using 2
          simp
          omega
  | assignVar hvalue hinScope hrest ih =>
      rename_i scope name value rest
      have hpresent : exprBoundNamesPresent value runtime.bindings :=
        exprBoundNamesPresent_of_scope hscope hinScope
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      have heval := eval_compileExpr_core_of_scope hvalue hexact hinScope hbounded hpresent hruntime
      rw [hvalueIR] at heval; simp [Except.toOption] at heval
      rcases hIR : evalIRExpr state valueIR with _ | valueNat
      · simp [hIR, Option.bind] at heval
      · simp [hIR, Option.bind] at heval
        have hEvalSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
          heval.symm
        let runtime' :=
          { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
        let state' := state.setVar name valueNat
        have hvalueLt := evalExpr_lt_evmModulus_core_of_scope hvalue hexact hinScope hbounded hpresent hruntime
        rw [hEvalSrc] at hvalueLt; simp at hvalueLt
        have hruntime' : runtimeStateMatchesIR fields runtime' state' :=
          runtimeStateMatchesIR_setVar_bindValue hruntime name valueNat
        have hexact' : bindingsExactlyMatchIRVarsOnScope (name :: scope) runtime'.bindings state' :=
          bindingsExactlyMatchIRVarsOnScope_setVar_bindValue hexact
        have hbounded' : bindingsBounded runtime'.bindings :=
          bindingsBounded_bindValue hbounded name valueNat hvalueLt
        have hscope' : scopeNamesPresent (name :: scope) runtime'.bindings :=
          scopeNamesPresent_cons_bindValue hscope
        have hincluded' : scopeNamesIncluded (name :: scope)
            (collectStmtNames (.assignVar name value) ++ inScopeNames) :=
          scopeNamesIncluded_collectStmtNames_assignVar hincluded
        rcases ih (extraFuel + sizeOf (YulStmt.assign name valueIR))
            (runtime := runtime') (state := state')
            (inScopeNames := collectStmtNames (.assignVar name value) ++ inScopeNames)
            hincluded' hscope' hexact' hbounded' hruntime' with
          ⟨tailIR, htailCompile, htailSem⟩
        refine ⟨[YulStmt.assign name valueIR] ++ tailIR, ?_, ?_⟩
        · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
          rw [hvalueIR]
          simp [htailCompile]
          exact rfl
        · have hstmt :
              execIRStmt (sizeOf ([YulStmt.assign name valueIR] ++ tailIR) + extraFuel) state
                (YulStmt.assign name valueIR) = .continue state' :=
            execIRStmt_assign_of_eval_nonzeroFuel
              (sizeOf ([YulStmt.assign name valueIR] ++ tailIR) + extraFuel) state name valueIR valueNat
              (sizeOf_singleton_append_extraFuel_ne_zero _ _ _)
              hIR
          have hirExec :=
            execIRStmts_singleton_append_of_execIRStmt_continue_wholeFuel
              extraFuel state state' (YulStmt.assign name valueIR) tailIR hstmt
          simp only [SourceSemantics.execStmtList, SourceSemantics.execStmt, hEvalSrc, hirExec]
          dsimp [runtime', state']
          convert htailSem using 2
          simp
          omega
  | require_ hcond hinScope hrest ih =>
      rename_i scope cond message rest
      have hpresent : exprBoundNamesPresent cond runtime.bindings :=
        exprBoundNamesPresent_of_scope hscope hinScope
      rcases compileExpr_core_ok hcond with ⟨condIR, hcondIR⟩
      have hCondEval := eval_compileExpr_core_of_scope hcond hexact hinScope hbounded hpresent hruntime
      rw [hcondIR] at hCondEval; simp [Except.toOption] at hCondEval
      rcases hCondIRVal : evalIRExpr state condIR with _ | condVal
      · simp [hCondIRVal, Option.bind] at hCondEval
      · simp [hCondIRVal, Option.bind] at hCondEval
        have hCondSrc : SourceSemantics.evalExpr fields runtime cond = some condVal :=
          hCondEval.symm
        rcases eval_compileRequireFailCond_core_of_scope hcond hexact hinScope
            hbounded hpresent hruntime with
          ⟨failCond, hfailCompile, hfailEval⟩
        have hincluded' : scopeNamesIncluded scope
            (collectStmtNames (.require cond message) ++ inScopeNames) :=
          scopeNamesIncluded_collectStmtNames_tail hincluded
        rcases ih (extraFuel + sizeOf (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)))
            (runtime := runtime) (state := state)
            (inScopeNames := collectStmtNames (.require cond message) ++ inScopeNames)
            hincluded' hscope hexact hbounded hruntime with
          ⟨tailIR, htailCompile, htailSem⟩
        refine ⟨[YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR,
          ?_, ?_⟩
        · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
          rw [hfailCompile]
          simp [htailCompile]
          exact rfl
        · by_cases hzero : condVal = 0
          · -- condVal = 0 → require fails → revert
            have hfailEval' : evalIRExpr state failCond = some 1 := by
              rw [hCondSrc, hzero] at hfailEval
              simpa [SourceSemantics.boolWord] using hfailEval
            have hfuelNe : sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) + extraFuel ≠ 0 :=
              sizeOf_singleton_append_extraFuel_ne_zero _ _ _
            -- if_ with true cond steps into the body
            have hIfStep :=
              execIRStmt_if_true_of_eval_nonzeroFuel
                (sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) + extraFuel)
                state failCond (CompilationModel.revertWithMessage message) 1
                hfuelNe hfailEval' (by omega)
            rcases execIRStmts_revertWithMessage_revert
                (fuel :=
                  sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) + extraFuel - 1)
                (state := state) message with
              ⟨revState, hrev⟩
            have hstmt :
                execIRStmt
                  (sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) + extraFuel)
                  state
                  (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) =
                    .revert revState := by
              rw [hIfStep, hrev]
            have hirExec :=
              execIRStmts_singleton_append_of_execIRStmt_revert_wholeFuel
                extraFuel state revState
                (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) tailIR
                hstmt
            simp only [SourceSemantics.execStmtList, SourceSemantics.execStmt, hCondSrc,
              show condVal = 0 from hzero, ite_true]
            rw [hirExec]
            simp [stmtResultMatchesIRExec]
          · -- condVal ≠ 0 → require passes → continue
            have hfailEval' : evalIRExpr state failCond = some 0 := by
              have : SourceSemantics.evalExpr fields runtime cond ≠ some 0 := by
                rw [hCondSrc]; simp [hzero]
              simpa [this, SourceSemantics.boolWord] using hfailEval
            have hfuelNe : sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) + extraFuel ≠ 0 :=
              sizeOf_singleton_append_extraFuel_ne_zero _ _ _
            have hstmt :
                execIRStmt
                  (sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) + extraFuel)
                  state
                  (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) =
                    .continue state :=
              execIRStmt_if_false_of_eval_nonzeroFuel
                (sizeOf ([YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] ++ tailIR) + extraFuel)
                state failCond (CompilationModel.revertWithMessage message) 0
                hfuelNe hfailEval' rfl
            have hirExec :=
              execIRStmts_singleton_append_of_execIRStmt_continue_wholeFuel
                extraFuel state state
                (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) tailIR
                hstmt
            simp only [SourceSemantics.execStmtList, SourceSemantics.execStmt, hCondSrc, hirExec]
            simp [hzero]
            convert htailSem using 2
            simp
            omega
  | return_ hvalue hinScope hrest =>
      rename_i scope value rest
      have hpresent : exprBoundNamesPresent value runtime.bindings :=
        exprBoundNamesPresent_of_scope hscope hinScope
      rcases compileExpr_core_ok hvalue with ⟨valueIR, hvalueIR⟩
      rcases compileStmtList_core_ok (fields := fields) (inScopeNames := collectStmtNames (.return value) ++ inScopeNames) hrest with
        ⟨tailIR, htailCompile⟩
      refine ⟨[ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
              , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] ++ tailIR,
        ?_, ?_⟩
      · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
        rw [hvalueIR]
        simp [htailCompile]
        exact rfl
      · exact stmtResultMatchesIRExec_compiled_return_core_append_wholeFuel_of_scope
          hvalue hvalueIR hexact hinScope hscope hbounded hruntime
  | stop hrest =>
      rename_i scope rest
      rcases compileStmtList_core_ok (fields := fields) (inScopeNames := collectStmtNames (.stop) ++ inScopeNames) hrest with
        ⟨tailIR, htailCompile⟩
      refine ⟨[YulStmt.expr (YulExpr.call "stop" [])] ++ tailIR, ?_, ?_⟩
      · simpa [CompilationModel.compileStmtList, CompilationModel.compileStmt, htailCompile]
      · exact stmtResultMatchesIRExec_compiled_stop_core_append_wholeFuel hruntime
  | ite hcond hinScope hthen helse hrest ih_then ih_else =>
      rename_i scope cond thenBranch elseBranch rest
      have hpresent : exprBoundNamesPresent cond runtime.bindings :=
        exprBoundNamesPresent_of_scope hscope hinScope
      rcases compileExpr_core_ok hcond with ⟨condIR, hcondIR⟩
      rcases compileStmtList_terminal_core_ok (fields := fields)
          (inScopeNames := inScopeNames) hthen with
        ⟨thenIR, hthenIR⟩
      rcases compileStmtList_terminal_core_ok (fields := fields)
          (inScopeNames := inScopeNames) helse with
        ⟨elseIR, helseIR⟩
      rcases compileStmtList_core_ok (fields := fields)
          (inScopeNames := collectStmtNames (.ite cond thenBranch elseBranch) ++ inScopeNames) hrest with
        ⟨tailIR, htailIR⟩
      have helseNonempty : elseBranch.isEmpty = false := by
        cases elseBranch with
        | nil => exfalso; exact stmtListTerminalCore_ne_nil helse rfl
        | cons => simp
      let tempName :=
        CompilationModel.pickFreshName "__ite_cond"
          (inScopeNames ++ collectExprNames cond ++
            collectStmtListNames thenBranch ++ collectStmtListNames elseBranch)
      refine ⟨[YulStmt.block
        [ YulStmt.let_ tempName condIR
        , YulStmt.if_ (YulExpr.ident tempName) thenIR
        , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]] ++ tailIR,
        ?_, ?_⟩
      · unfold CompilationModel.compileStmtList CompilationModel.compileStmt
        rw [hcondIR, hthenIR, helseIR]
        simp [helseNonempty, htailIR, tempName]
        exact rfl
      · -- Evaluate the condition
        have hCondEval := eval_compileExpr_core_of_scope hcond hexact hinScope hbounded hpresent hruntime
        rw [hcondIR] at hCondEval; simp [Except.toOption] at hCondEval
        rcases hCondIRVal : evalIRExpr state condIR with _ | condVal
        · simp [hCondIRVal, Option.bind] at hCondEval
        · simp [hCondIRVal, Option.bind] at hCondEval
          have hCondSrc : SourceSemantics.evalExpr fields runtime cond = some condVal :=
            hCondEval.symm
          have hexact' : bindingsExactlyMatchIRVarsOnScope scope runtime.bindings
              (state.setVar tempName condVal) :=
            bindingsExactlyMatchIRVarsOnScope_setCompiledTerminalIteTemp_irrelevant hexact hincluded
          by_cases hcondZero : condVal = 0
          · -- Condition is false → take else branch
            rcases ih_else (extraFuel +
                sizeOf (YulStmt.let_ tempName condIR) +
                sizeOf (YulStmt.if_ (YulExpr.ident tempName) thenIR) +
                sizeOf (YulExpr.call "iszero" [YulExpr.ident tempName]) +
                sizeOf tailIR + 1)
                (runtime := runtime) (state := state.setVar tempName condVal)
                (inScopeNames := inScopeNames)
                hincluded hscope hexact' hbounded hruntime with
              ⟨elseIR', helseCompile', helseSem⟩
            have helseEq : elseIR' = elseIR := by
              have := helseCompile'; rw [helseIR] at this; exact (Except.ok.inj this).symm
            rw [helseEq] at helseSem
            -- Prove fuel equality to convert IH fuel into helper's expected fuel
            have hfuelEq : sizeOf elseIR +
                  (extraFuel +
                    sizeOf (YulStmt.let_ tempName condIR) +
                    sizeOf (YulStmt.if_ (YulExpr.ident tempName) thenIR) +
                    sizeOf (YulExpr.call "iszero" [YulExpr.ident tempName]) +
                    sizeOf tailIR + 1) + 1 =
                sizeOf elseIR +
                  (sizeOf
                    ([YulStmt.block
                        [ YulStmt.let_ tempName condIR
                        , YulStmt.if_ (YulExpr.ident tempName) thenIR
                        , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR
                        ]] ++ tailIR) -
                    (sizeOf elseIR + 5) + extraFuel) := by
              simp only [List.singleton_append]
              have hinner : sizeOf (YulStmt.block
                      [ YulStmt.let_ tempName condIR
                      , YulStmt.if_ (YulExpr.ident tempName) thenIR
                      , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR
                      ] :: tailIR) -
                    (sizeOf elseIR + 5) =
                  sizeOf (YulStmt.let_ tempName condIR) +
                  sizeOf (YulStmt.if_ (YulExpr.ident tempName) thenIR) +
                  sizeOf (YulExpr.call "iszero" [YulExpr.ident tempName]) +
                  sizeOf tailIR + 2 := by
                simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec,
                  YulStmt.block.sizeOf_spec, YulStmt.if_.sizeOf_spec,
                  YulStmt.let_.sizeOf_spec,
                  YulExpr.call.sizeOf_spec, YulExpr.ident.sizeOf_spec]
                omega
              rw [hinner]
              omega
            rw [show execIRStmts
                  (sizeOf elseIR +
                    (extraFuel +
                      sizeOf (YulStmt.let_ tempName condIR) +
                      sizeOf (YulStmt.if_ (YulExpr.ident tempName) thenIR) +
                      sizeOf (YulExpr.call "iszero" [YulExpr.ident tempName]) +
                      sizeOf tailIR + 1) + 1)
                  (state.setVar tempName condVal) elseIR =
                execIRStmts
                  (sizeOf elseIR +
                    (sizeOf
                      ([YulStmt.block
                          [ YulStmt.let_ tempName condIR
                          , YulStmt.if_ (YulExpr.ident tempName) thenIR
                          , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR
                          ]] ++ tailIR) -
                      (sizeOf elseIR + 5) + extraFuel))
                  (state.setVar tempName condVal) elseIR from by
              rw [hfuelEq]] at helseSem
            exact stmtResultMatchesIRExec_compiled_terminal_ite_else
              (scope := scope)
              (rest := rest)
              (tempName := tempName)
              (condIR := condIR)
              (thenIR := thenIR)
              (tailIR := tailIR)
              helse helseSem hCondSrc
              (by simp [hcondZero])
              hCondIRVal hcondZero rfl
          · -- Condition is true → take then branch
            rcases ih_then (extraFuel +
                sizeOf (YulStmt.let_ tempName condIR) +
                sizeOf (YulExpr.ident tempName) +
                sizeOf (YulStmt.if_
                    (YulExpr.call "iszero" [YulExpr.ident tempName])
                    elseIR) +
                sizeOf tailIR + 2)
                (runtime := runtime) (state := state.setVar tempName condVal)
                (inScopeNames := inScopeNames)
                hincluded hscope hexact' hbounded hruntime with
              ⟨thenIR', hthenCompile', hthenSem⟩
            have hthenEq : thenIR' = thenIR := by
              have := hthenCompile'; rw [hthenIR] at this; exact (Except.ok.inj this).symm
            rw [hthenEq] at hthenSem
            -- Prove fuel equality to convert IH fuel into helper's expected fuel
            have hfuelEq : sizeOf thenIR +
                  (extraFuel +
                    sizeOf (YulStmt.let_ tempName condIR) +
                    sizeOf (YulExpr.ident tempName) +
                    sizeOf (YulStmt.if_
                        (YulExpr.call "iszero" [YulExpr.ident tempName])
                        elseIR) +
                    sizeOf tailIR + 2) + 1 =
                sizeOf thenIR +
                  (sizeOf
                    ([YulStmt.block
                        [ YulStmt.let_ tempName condIR
                        , YulStmt.if_ (YulExpr.ident tempName) thenIR
                        , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR
                        ]] ++ tailIR) -
                    (sizeOf thenIR + 5) + extraFuel) + 1 := by
              simp only [List.singleton_append]
              have hinner : sizeOf (YulStmt.block
                      [ YulStmt.let_ tempName condIR
                      , YulStmt.if_ (YulExpr.ident tempName) thenIR
                      , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR
                      ] :: tailIR) -
                    (sizeOf thenIR + 5) =
                  sizeOf (YulStmt.let_ tempName condIR) +
                  sizeOf (YulExpr.ident tempName) +
                  sizeOf (YulStmt.if_
                      (YulExpr.call "iszero" [YulExpr.ident tempName])
                      elseIR) +
                  sizeOf tailIR + 2 := by
                simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec,
                  YulStmt.block.sizeOf_spec, YulStmt.if_.sizeOf_spec,
                  YulStmt.let_.sizeOf_spec,
                  YulExpr.call.sizeOf_spec, YulExpr.ident.sizeOf_spec]
                omega
              rw [hinner]
              omega
            rw [show execIRStmts
                  (sizeOf thenIR +
                    (extraFuel +
                      sizeOf (YulStmt.let_ tempName condIR) +
                      sizeOf (YulExpr.ident tempName) +
                      sizeOf (YulStmt.if_
                          (YulExpr.call "iszero" [YulExpr.ident tempName])
                          elseIR) +
                      sizeOf tailIR + 2) + 1)
                  (state.setVar tempName condVal) thenIR =
                execIRStmts
                  (sizeOf thenIR +
                    (sizeOf
                      ([YulStmt.block
                          [ YulStmt.let_ tempName condIR
                          , YulStmt.if_ (YulExpr.ident tempName) thenIR
                          , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR
                          ]] ++ tailIR) -
                      (sizeOf thenIR + 5) + extraFuel) + 1)
                  (state.setVar tempName condVal) thenIR from by
              rw [hfuelEq]] at hthenSem
            exact stmtResultMatchesIRExec_compiled_terminal_ite_then
              (scope := scope)
              (rest := rest)
              (tempName := tempName)
              (condIR := condIR)
              (elseIR := elseIR)
              (tailIR := tailIR)
              hthen hthenSem hCondSrc
              (by simp [hcondZero])
              hCondIRVal hcondZero rfl

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
  cases sourceResult <;> cases irResult <;>
    simp [stmtResultMatchesIRExec] at hmatch
  · rcases hmatch with
      ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
    simp [stmtResultToSourceResult, sourceResultMatchesIRResult, irResultOfExecResult,
      SourceSemantics.successResult, SourceSemantics.encodeStorage,
      hstorage, hevents, hret]
  · rcases hmatch with
      ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
    simp [stmtResultToSourceResult, sourceResultMatchesIRResult, irResultOfExecResult,
      SourceSemantics.successResult, SourceSemantics.encodeStorage,
      hstorage, hevents]
  · rcases hmatch with
      ⟨hvalue, hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret,
        hevents⟩
    simp [stmtResultToSourceResult, sourceResultMatchesIRResult, irResultOfExecResult,
      SourceSemantics.successResult, SourceSemantics.encodeStorage,
      hvalue, hstorage, hevents]
  · simp [stmtResultToSourceResult, sourceResultMatchesIRResult, irResultOfExecResult,
      SourceSemantics.revertedResult, hrollbackStorage, hrollbackEvents]

end FunctionBody

end Compiler.Proofs.IRGeneration
