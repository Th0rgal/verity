import Compiler.CompilationModel.ExpressionCompile
import Compiler.Proofs.IRGeneration.ParamLoading
import Compiler.Proofs.IRGeneration.SourceSemantics

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

def bindingsMatchIRVars
    (bindings : List (String × Nat))
    (state : IRState) : Prop :=
  ∀ name, (state.getVar name).getD 0 = SourceSemantics.lookupValue bindings name

theorem bindingsExactlyMatchIRVars_implies_bindingsMatchIRVars
    {bindings : List (String × Nat)}
    {state : IRState}
    (hexact : bindingsExactlyMatchIRVars bindings state) :
    bindingsMatchIRVars bindings state := by
  intro name
  rw [hexact name]
  rfl

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
