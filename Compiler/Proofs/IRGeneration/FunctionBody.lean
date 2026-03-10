import Compiler.CompilationModel.ExpressionCompile
import Compiler.Proofs.IRGeneration.ParamLoading
import Compiler.Proofs.IRGeneration.SourceSemantics
import Compiler.Proofs.IRGeneration.SupportedSpec

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

namespace FunctionBody

def lookupBinding? (bindings : List (String × Nat)) (name : String) : Option Nat :=
  bindings.find? (fun entry => entry.1 == name) |>.map Prod.snd

mutual
def exprBoundNames : Expr → List String
  | .param name => [name]
  | .localVar name => [name]
  | .mapping _ key | .mappingWord _ key _ | .mappingPackedWord _ key _ _ | .mappingUint _ key
  | .structMember _ key _ | .extcodesize key | .mload key | .tload key
  | .calldataload key | .returndataOptionalBoolAt key => exprBoundNames key
  | .mapping2 _ key1 key2 | .mapping2Word _ key1 key2 _ | .structMember2 _ key1 key2 _ =>
      exprBoundNames key1 ++ exprBoundNames key2
  | .keccak256 offset size =>
      exprBoundNames offset ++ exprBoundNames size
  | .call gas target value inOffset inSize outOffset outSize =>
      exprBoundNames gas ++ exprBoundNames target ++ exprBoundNames value ++
        exprBoundNames inOffset ++ exprBoundNames inSize ++
        exprBoundNames outOffset ++ exprBoundNames outSize
  | .staticcall gas target inOffset inSize outOffset outSize =>
      exprBoundNames gas ++ exprBoundNames target ++ exprBoundNames inOffset ++
        exprBoundNames inSize ++ exprBoundNames outOffset ++ exprBoundNames outSize
  | .delegatecall gas target inOffset inSize outOffset outSize =>
      exprBoundNames gas ++ exprBoundNames target ++ exprBoundNames inOffset ++
        exprBoundNames inSize ++ exprBoundNames outOffset ++ exprBoundNames outSize
  | .externalCall _ args | .internalCall _ args => exprListBoundNames args
  | .arrayElement name index => name :: exprBoundNames index
  | .arrayLength name => [name]
  | .add a b | .sub a b | .mul a b | .div a b | .mod a b
  | .bitAnd a b | .bitOr a b | .bitXor a b | .eq a b
  | .ge a b | .gt a b | .lt a b | .le a b
  | .logicalAnd a b | .logicalOr a b | .wMulDown a b
  | .wDivUp a b | .min a b | .max a b
  | .shl a b | .shr a b =>
      exprBoundNames a ++ exprBoundNames b
  | .mulDivDown a b c | .mulDivUp a b c =>
      exprBoundNames a ++ exprBoundNames b ++ exprBoundNames c
  | .bitNot a | .logicalNot a => exprBoundNames a
  | .ite cond thenVal elseVal =>
      exprBoundNames cond ++ exprBoundNames thenVal ++ exprBoundNames elseVal
  | .literal _ | .constructorArg _ | .storage _ | .storageAddr _ | .caller
  | .contractAddress | .chainid | .msgValue | .blockTimestamp | .blockNumber
  | .blobbasefee | .calldatasize | .returndataSize => []
termination_by expr => sizeOf expr
decreasing_by
  all_goals simp_wf
  all_goals omega

def exprListBoundNames : List Expr → List String
  | [] => []
  | expr :: rest => exprBoundNames expr ++ exprListBoundNames rest
termination_by exprs => sizeOf exprs
decreasing_by
  all_goals simp_wf
  all_goals omega
end

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
  rcases hmatch with ⟨_, hsender, _, _, _, _, _, _, _⟩
  rw [show SourceSemantics.evalExpr fields runtime (.caller) = runtime.world.sender.val by rfl]
  simp [evalIRExpr, evalIRCall, evalIRExprs,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext, hsender]

theorem evalIRExpr_contractAddress_of_runtimeStateMatchesIR
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (YulExpr.call "address" []) =
      some (SourceSemantics.evalExpr fields runtime (.contractAddress)) := by
  rcases hmatch with ⟨_, _, _, hthis, _, _, _, _, _⟩
  have hthisLt : runtime.world.thisAddress.val < Compiler.Constants.evmModulus := by
    have haddrLt : runtime.world.thisAddress.val < Verity.Core.ADDRESS_MODULUS := by
      simpa [Verity.Core.Address.modulus] using
        Verity.Core.Address.val_lt_modulus runtime.world.thisAddress
    have hmodLt : Verity.Core.ADDRESS_MODULUS < Compiler.Constants.evmModulus := by
      norm_num [Verity.Core.ADDRESS_MODULUS, Compiler.Constants.evmModulus]
    exact Nat.lt_trans haddrLt hmodLt
  rw [show SourceSemantics.evalExpr fields runtime (.contractAddress) = runtime.world.thisAddress.val by rfl]
  simp [evalIRExpr, evalIRCall, evalIRExprs,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext, hthis, Nat.mod_eq_of_lt hthisLt]

theorem evalIRExpr_msgValue_of_runtimeStateMatchesIR
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (YulExpr.call "callvalue" []) =
      some (SourceSemantics.evalExpr fields runtime (.msgValue)) := by
  rcases hmatch with ⟨_, _, hmsgValue, _, _, _, _, _, _⟩
  rw [show SourceSemantics.evalExpr fields runtime (.msgValue) = runtime.world.msgValue.val by rfl]
  have hmsgValueLt : runtime.world.msgValue.val < Compiler.Constants.evmModulus := by
    simpa [Verity.Core.Uint256.modulus, Compiler.Constants.evmModulus] using
      runtime.world.msgValue.isLt
  simp [evalIRExpr, evalIRCall, evalIRExprs,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext, hmsgValue, Nat.mod_eq_of_lt hmsgValueLt]

theorem evalIRExpr_blockTimestamp_of_runtimeStateMatchesIR
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (YulExpr.call "timestamp" []) =
      some (SourceSemantics.evalExpr fields runtime (.blockTimestamp)) := by
  rcases hmatch with ⟨_, _, _, _, htimestamp, _, _, _, _⟩
  rw [show SourceSemantics.evalExpr fields runtime (.blockTimestamp) =
      runtime.world.blockTimestamp.val by rfl]
  have htimestampLt : runtime.world.blockTimestamp.val < Compiler.Constants.evmModulus := by
    simpa [Verity.Core.Uint256.modulus, Compiler.Constants.evmModulus] using
      runtime.world.blockTimestamp.isLt
  simp [evalIRExpr, evalIRCall, evalIRExprs,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext, htimestamp, Nat.mod_eq_of_lt htimestampLt]

theorem evalIRExpr_blockNumber_of_runtimeStateMatchesIR
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (YulExpr.call "number" []) =
      some (SourceSemantics.evalExpr fields runtime (.blockNumber)) := by
  rcases hmatch with ⟨_, _, _, _, _, hnumber, _, _, _⟩
  rw [show SourceSemantics.evalExpr fields runtime (.blockNumber) =
      runtime.world.blockNumber.val by rfl]
  have hnumberLt : runtime.world.blockNumber.val < Compiler.Constants.evmModulus := by
    simpa [Verity.Core.Uint256.modulus, Compiler.Constants.evmModulus] using
      runtime.world.blockNumber.isLt
  simp [evalIRExpr, evalIRCall, evalIRExprs,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext, hnumber, Nat.mod_eq_of_lt hnumberLt]

theorem evalIRExpr_chainid_of_runtimeStateMatchesIR
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (YulExpr.call "chainid" []) =
      some (SourceSemantics.evalExpr fields runtime (.chainid)) := by
  rcases hmatch with ⟨_, _, _, _, _, _, hchain, _, _⟩
  rw [show SourceSemantics.evalExpr fields runtime (.chainid) = runtime.world.chainId.val by rfl]
  have hchainLt : runtime.world.chainId.val < Compiler.Constants.evmModulus := by
    simpa [Verity.Core.Uint256.modulus, Compiler.Constants.evmModulus] using
      runtime.world.chainId.isLt
  simp [evalIRExpr, evalIRCall, evalIRExprs,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext, hchain, Nat.mod_eq_of_lt hchainLt]

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

/-- Expression fragment whose `compileExpr` correctness is already structurally
closed: scalar leaves, runtime builtins, arithmetic, comparisons, and boolean
operators. Storage/mapping/dynamic forms still require separate invariants. -/
inductive ExprCompileCore : Expr → Prop where
  | literal (value : Nat) : ExprCompileCore (.literal value)
  | param (name : String) : ExprCompileCore (.param name)
  | localVar (name : String) : ExprCompileCore (.localVar name)
  | caller : ExprCompileCore .caller
  | contractAddress : ExprCompileCore .contractAddress
  | msgValue : ExprCompileCore .msgValue
  | blockTimestamp : ExprCompileCore .blockTimestamp
  | blockNumber : ExprCompileCore .blockNumber
  | chainid : ExprCompileCore .chainid
  | add {lhs rhs : Expr} :
      ExprCompileCore lhs → ExprCompileCore rhs → ExprCompileCore (.add lhs rhs)
  | sub {lhs rhs : Expr} :
      ExprCompileCore lhs → ExprCompileCore rhs → ExprCompileCore (.sub lhs rhs)
  | mul {lhs rhs : Expr} :
      ExprCompileCore lhs → ExprCompileCore rhs → ExprCompileCore (.mul lhs rhs)
  | div {lhs rhs : Expr} :
      ExprCompileCore lhs → ExprCompileCore rhs → ExprCompileCore (.div lhs rhs)
  | mod {lhs rhs : Expr} :
      ExprCompileCore lhs → ExprCompileCore rhs → ExprCompileCore (.mod lhs rhs)
  | eq {lhs rhs : Expr} :
      ExprCompileCore lhs → ExprCompileCore rhs → ExprCompileCore (.eq lhs rhs)
  | lt {lhs rhs : Expr} :
      ExprCompileCore lhs → ExprCompileCore rhs → ExprCompileCore (.lt lhs rhs)
  | gt {lhs rhs : Expr} :
      ExprCompileCore lhs → ExprCompileCore rhs → ExprCompileCore (.gt lhs rhs)
  | ge {lhs rhs : Expr} :
      ExprCompileCore lhs → ExprCompileCore rhs → ExprCompileCore (.ge lhs rhs)
  | le {lhs rhs : Expr} :
      ExprCompileCore lhs → ExprCompileCore rhs → ExprCompileCore (.le lhs rhs)
  | logicalNot {expr : Expr} :
      ExprCompileCore expr → ExprCompileCore (.logicalNot expr)
  | logicalAnd {lhs rhs : Expr} :
      ExprCompileCore lhs → ExprCompileCore rhs → ExprCompileCore (.logicalAnd lhs rhs)
  | logicalOr {lhs rhs : Expr} :
      ExprCompileCore lhs → ExprCompileCore rhs → ExprCompileCore (.logicalOr lhs rhs)

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
        some (SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime cond = 0)) :=
  eval_compileRequireFailCond_core_onExpr hcore
    (bindingsExactlyMatchIRVars_implies_onExpr hexact) hbounded hpresent hruntime

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

def scopeNamesPresent (scope : List String) (bindings : List (String × Nat)) : Prop :=
  ∀ name, name ∈ scope → ∃ value, lookupBinding? bindings name = some value

def exprBoundNamesInScope (expr : Expr) (scope : List String) : Prop :=
  ∀ name, name ∈ exprBoundNames expr → name ∈ scope

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

theorem exprBoundNamesPresent_of_scope
    {expr : Expr}
    {scope : List String}
    {bindings : List (String × Nat)}
    (hscope : scopeNamesPresent scope bindings)
    (hinScope : exprBoundNamesInScope expr scope) :
    exprBoundNamesPresent expr bindings := by
  intro name hname
  exact hscope name (hinScope name hname)

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

/-- Sequential statement fragment that can already be proved generically from the
expression core. The scope tracks names available to later expressions. -/
inductive StmtListCompileCore : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListCompileCore scope []
  | letVar {scope : List String} {name : String} {value : Expr} {rest : List Stmt} :
      ExprCompileCore value →
      exprBoundNamesInScope value scope →
      StmtListCompileCore (name :: scope) rest →
      StmtListCompileCore scope (.letVar name value :: rest)
  | assignVar {scope : List String} {name : String} {value : Expr} {rest : List Stmt} :
      ExprCompileCore value →
      exprBoundNamesInScope value scope →
      StmtListCompileCore (name :: scope) rest →
      StmtListCompileCore scope (.assignVar name value :: rest)
  | require_ {scope : List String} {cond : Expr} {message : String} {rest : List Stmt} :
      ExprCompileCore cond →
      exprBoundNamesInScope cond scope →
      StmtListCompileCore scope rest →
      StmtListCompileCore scope (.require cond message :: rest)
  | return_ {scope : List String} {value : Expr} {rest : List Stmt} :
      ExprCompileCore value →
      exprBoundNamesInScope value scope →
      StmtListCompileCore scope rest →
      StmtListCompileCore scope (.return value :: rest)
  | stop {scope : List String} {rest : List Stmt} :
      StmtListCompileCore scope rest →
      StmtListCompileCore scope (.stop :: rest)

/-- Core statement lists whose execution is guaranteed to terminate before
reaching the end of the list. This is the smallest useful extension needed
to simulate `Stmt.ite` without threading an exact-global bindings invariant
through the compiler-generated `__ite_cond` temporary. -/
inductive StmtListTerminalCore : List String → List Stmt → Prop where
  | letVar {scope : List String} {name : String} {value : Expr} {rest : List Stmt} :
      ExprCompileCore value →
      exprBoundNamesInScope value scope →
      StmtListTerminalCore (name :: scope) rest →
      StmtListTerminalCore scope (.letVar name value :: rest)
  | assignVar {scope : List String} {name : String} {value : Expr} {rest : List Stmt} :
      ExprCompileCore value →
      exprBoundNamesInScope value scope →
      StmtListTerminalCore (name :: scope) rest →
      StmtListTerminalCore scope (.assignVar name value :: rest)
  | require_ {scope : List String} {cond : Expr} {message : String} {rest : List Stmt} :
      ExprCompileCore cond →
      exprBoundNamesInScope cond scope →
      StmtListTerminalCore scope rest →
      StmtListTerminalCore scope (.require cond message :: rest)
  | return_ {scope : List String} {value : Expr} {rest : List Stmt} :
      ExprCompileCore value →
      exprBoundNamesInScope value scope →
      StmtListCompileCore scope rest →
      StmtListTerminalCore scope (.return value :: rest)
  | stop {scope : List String} {rest : List Stmt} :
      StmtListCompileCore scope rest →
      StmtListTerminalCore scope (.stop :: rest)
  | ite {scope : List String} {cond : Expr}
      {thenBranch elseBranch rest : List Stmt} :
      ExprCompileCore cond →
      exprBoundNamesInScope cond scope →
      StmtListTerminalCore scope thenBranch →
      StmtListTerminalCore scope elseBranch →
      StmtListCompileCore scope rest →
      StmtListTerminalCore scope (.ite cond thenBranch elseBranch :: rest)

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

private theorem yulStmtList_sizeOf_cons_ge_tailFuel
    (stmt : YulStmt)
    (rest : List YulStmt) :
    sizeOf rest + 1 ≤ sizeOf (stmt :: rest) := by
  simp
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

private theorem execIRStmt_block_of_execIRStmts_continue
    (fuel : Nat) (state next : IRState) (body : List YulStmt)
    (hbody : execIRStmts fuel state body = .continue next) :
    execIRStmt (Nat.succ fuel) state (YulStmt.block body) = .continue next := by
  simpa [execIRStmt] using hbody

private theorem execIRStmt_block_of_execIRStmts_return
    (fuel : Nat) (state next : IRState) (body : List YulStmt) (value : Nat)
    (hbody : execIRStmts fuel state body = .return value next) :
    execIRStmt (Nat.succ fuel) state (YulStmt.block body) = .return value next := by
  simpa [execIRStmt] using hbody

private theorem execIRStmt_block_of_execIRStmts_stop
    (fuel : Nat) (state next : IRState) (body : List YulStmt)
    (hbody : execIRStmts fuel state body = .stop next) :
    execIRStmt (Nat.succ fuel) state (YulStmt.block body) = .stop next := by
  simpa [execIRStmt] using hbody

private theorem execIRStmt_block_of_execIRStmts_revert
    (fuel : Nat) (state next : IRState) (body : List YulStmt)
    (hbody : execIRStmts fuel state body = .revert next) :
    execIRStmt (Nat.succ fuel) state (YulStmt.block body) = .revert next := by
  simpa [execIRStmt] using hbody

private theorem execIRStmt_if_true_of_eval
    (fuel : Nat) (state : IRState) (cond : YulExpr) (body : List YulStmt) (value : Nat)
    (hcond : evalIRExpr state cond = some value)
    (hvalue : value ≠ 0) :
    execIRStmt (Nat.succ fuel) state (YulStmt.if_ cond body) = execIRStmts fuel state body := by
  simp [execIRStmt, hcond, hvalue]

private theorem execIRStmt_if_false_of_eval
    (fuel : Nat) (state : IRState) (cond : YulExpr) (body : List YulStmt) (value : Nat)
    (hcond : evalIRExpr state cond = some value)
    (hvalue : value = 0) :
    execIRStmt (Nat.succ fuel) state (YulStmt.if_ cond body) = .continue state := by
  simp [execIRStmt, hcond, hvalue]

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
    rcases hmatch with ⟨hstorage, _, _, _, _, _, hret, ⟨hnone, hevents⟩⟩
    refine ⟨rfl, hnone.symm, ?_, hevents.symm⟩
    simpa [sourceResultMatchesIRResult, stmtResultToSourceResult,
      SourceSemantics.successResult, SourceSemantics.encodeStorage] using hstorage.symm
  ·
    rcases hmatch with ⟨hstorage, _, _, _, _, _, hret, ⟨hnone, hevents⟩⟩
    refine ⟨rfl, rfl, ?_, hevents.symm⟩
    simpa [sourceResultMatchesIRResult, stmtResultToSourceResult,
      SourceSemantics.successResult, SourceSemantics.encodeStorage] using hstorage.symm
  ·
    rcases hmatch with ⟨rfl, hstorage, _, _, _, _, _, hret, ⟨hnone, hevents⟩⟩
    refine ⟨rfl, rfl, ?_, hevents.symm⟩
    simpa [sourceResultMatchesIRResult, stmtResultToSourceResult,
      SourceSemantics.successResult, SourceSemantics.encodeStorage] using hstorage.symm
  ·
    refine ⟨rfl, rfl, hrollbackStorage.symm, hrollbackEvents.symm⟩

end FunctionBody

end Compiler.Proofs.IRGeneration
