import Compiler.CompilationModel.ParamLoading
import Compiler.Proofs.IRGeneration.SourceSemantics

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

namespace ParamLoading

def applyBindingsToIRState (state : IRState) : List (String × Nat) → IRState
  | [] => state
  | (name, value) :: rest =>
      applyBindingsToIRState (state.setVar name value) rest

@[simp] theorem uint256_modulus_eq_evm :
    Verity.Core.Uint256.modulus = Compiler.Constants.evmModulus := by
  rfl

@[simp] theorem wordNormalize_eq_mod (n : Nat) :
    SourceSemantics.wordNormalize n = n % Compiler.Constants.evmModulus := by
  change n % Verity.Core.UINT256_MODULUS = n % Compiler.Constants.evmModulus
  rfl

private theorem foldl_add_eq (xs : List Nat) (init : Nat) :
    xs.foldl (· + ·) init = xs.foldl (· + ·) 0 + init := by
  induction xs generalizing init with
  | nil =>
      simp
  | cons x rest ih =>
      calc
        (x :: rest).foldl (· + ·) init
            = rest.foldl (· + ·) (init + x) := by simp [List.foldl]
        _ = rest.foldl (· + ·) 0 + (init + x) := ih (init + x)
        _ = rest.foldl (· + ·) 0 + x + init := by omega
        _ = rest.foldl (· + ·) x + init := by
              rw [ih x]
        _ = (x :: rest).foldl (· + ·) 0 + init := by simp [List.foldl]

theorem bindSupportedParams_some_length
    {params : List Param} {args : List Nat} {bindings : List (String × Nat)}
    (hbind : SourceSemantics.bindSupportedParams params args = some bindings) :
    params.length ≤ args.length := by
  induction params generalizing args bindings with
  | nil =>
      exact Nat.zero_le _
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
              exact Nat.succ_le_succ (ih hrest)

theorem supportedParamHeadSize_eq_32
    {ty : ParamType} (hsupported : SupportedExternalParamType ty) :
    paramHeadSize ty = 32 := by
  cases ty <;> simp [SupportedExternalParamType] at hsupported <;>
    simp [paramHeadSize]

theorem supportedScalarHeadSize_eq
    (params : List Param)
    (hsupported : ∀ param ∈ params, SupportedExternalParamType param.ty) :
    (params.map (fun p => paramHeadSize p.ty)).foldl (· + ·) 0 = 32 * params.length := by
  induction params with
  | nil =>
      simp
  | cons param rest ih =>
      have hparam : SupportedExternalParamType param.ty := hsupported param (by simp)
      have hrest : ∀ next ∈ rest, SupportedExternalParamType next.ty := by
        intro next hnext
        exact hsupported next (by simp [hnext])
      calc
        (List.map (fun p => paramHeadSize p.ty) (param :: rest)).foldl (· + ·) 0
            = paramHeadSize param.ty + (List.map (fun p => paramHeadSize p.ty) rest).foldl (· + ·) 0 := by
                simpa [Nat.add_comm] using
                  (foldl_add_eq (List.map (fun p => paramHeadSize p.ty) rest) (paramHeadSize param.ty))
        _ = 32 + (List.map (fun p => paramHeadSize p.ty) rest).foldl (· + ·) 0 := by
              rw [supportedParamHeadSize_eq_32 hparam]
        _ = 32 + 32 * rest.length := by
              rw [ih hrest]
        _ = 32 * (rest.length + 1) := by
              omega
        _ = 32 * (param :: rest).length := by
              simp

@[simp] theorem calldataloadWord_aligned
    (selector : Nat) (calldata : List Nat) (idx : Nat) :
    Compiler.Proofs.YulGeneration.calldataloadWord selector calldata (4 + 32 * idx) =
      calldata.getD idx 0 % Compiler.Constants.evmModulus := by
  have hlt : ¬ 4 + 32 * idx < 4 := by omega
  simp [Compiler.Proofs.YulGeneration.calldataloadWord, hlt]

theorem exec_genScalarLoad_supported
    (state : IRState) (name : String) (ty : ParamType) (idx value : Nat)
    (hsupported : SupportedExternalParamType ty)
    (hdecode : SourceSemantics.decodeSupportedParamWord ty (state.calldata.getD idx 0) = some value) :
    execIRStmts ((genScalarLoad (fun pos => YulExpr.call "calldataload" [pos]) name ty (4 + 32 * idx)).length + 1)
      state
      (genScalarLoad (fun pos => YulExpr.call "calldataload" [pos]) name ty (4 + 32 * idx)) =
      .continue (state.setVar name value) := by
  cases ty <;> try cases hsupported
  case uint256 =>
    have hvalue : value = state.calldata.getD idx 0 % Compiler.Constants.evmModulus := by
      simpa [SourceSemantics.decodeSupportedParamWord, SourceSemantics.wordNormalize,
        Verity.Core.UINT256_MODULUS, uint256_modulus_eq_evm] using hdecode.symm
    cases hvalue
    simp [genScalarLoad, execIRStmts, execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext, calldataloadWord_aligned]
  case uint8 =>
    simp [SourceSemantics.decodeSupportedParamWord, SourceSemantics.wordNormalize,
      SourceSemantics.uint8Modulus] at hdecode
    subst value
    have h255 : (255 : Nat) % Compiler.Constants.evmModulus = 255 := by
      norm_num [Compiler.Constants.evmModulus]
    simp [genScalarLoad, execIRStmts, execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext, calldataloadWord_aligned, h255]
  case address =>
    simp [SourceSemantics.decodeSupportedParamWord, SourceSemantics.wordNormalize] at hdecode
    subst value
    have hmask : Compiler.Constants.addressMask % Compiler.Constants.evmModulus =
        Compiler.Constants.addressMask := by
      have hlt : Compiler.Constants.addressMask < Compiler.Constants.evmModulus := by
        dsimp [Compiler.Constants.addressMask, Compiler.Constants.evmModulus]
        omega
      exact Nat.mod_eq_of_lt hlt
    simp [genScalarLoad, execIRStmts, execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext, calldataloadWord_aligned, hmask]
  case bytes32 =>
    have hvalue : value = state.calldata.getD idx 0 % Compiler.Constants.evmModulus := by
      simpa [SourceSemantics.decodeSupportedParamWord, SourceSemantics.wordNormalize,
        Verity.Core.UINT256_MODULUS, uint256_modulus_eq_evm] using hdecode.symm
    cases hvalue
    simp [genScalarLoad, execIRStmts, execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext, calldataloadWord_aligned]

private theorem getD_eq_of_drop_eq_cons
    {xs : List Nat} {idx arg : Nat} {rest : List Nat}
    (hdrop : xs.drop idx = arg :: rest) :
    xs.getD idx 0 = arg := by
  have hlookup : xs[idx]? = some arg := by
    simpa [hdrop, Nat.zero_add] using
      (List.getElem?_drop (xs := xs) (i := idx) (j := 0)).symm
  simp [List.getD, hlookup]

private theorem drop_succ_eq_of_drop_eq_cons
    {xs : List Nat} {idx arg : Nat} {rest : List Nat}
    (hdrop : xs.drop idx = arg :: rest) :
    xs.drop (idx + 1) = rest := by
  calc
    xs.drop (idx + 1) = (xs.drop idx).drop 1 := by
      simpa [Nat.add_comm] using
        (List.drop_drop (i := 1) (j := idx) (l := xs)).symm
    _ = rest := by simp [hdrop]

private theorem genScalarLoad_length_supported
    (name : String) {ty : ParamType} (offset : Nat)
    (hsupported : SupportedExternalParamType ty) :
    (genScalarLoad (fun pos => YulExpr.call "calldataload" [pos]) name ty offset).length = 1 := by
  cases ty <;> simp [genScalarLoad, SupportedExternalParamType] at hsupported ⊢

private theorem supportedExternalParamType_cases
    {ty : ParamType} (hsupported : SupportedExternalParamType ty) :
    ty = .uint256 ∨ ty = .uint8 ∨ ty = .address ∨ ty = .bytes32 := by
  cases ty <;> simp [SupportedExternalParamType] at hsupported ⊢

private theorem execIRStmts_cons_of_execIRStmt_continue
    (state next : IRState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execIRStmt (rest.length + 1) state stmt = .continue next) :
    execIRStmts (rest.length + 2) state (stmt :: rest) =
      execIRStmts (rest.length + 1) next rest := by
  simp [execIRStmts, hstmt]

private theorem exec_genScalarLoad_supported_then_uint256
    (state : IRState) (rest : List YulStmt) (name : String) (idx value : Nat)
    (hdecode : SourceSemantics.decodeSupportedParamWord .uint256 (state.calldata.getD idx 0) = some value) :
    execIRStmts ((genScalarLoad (fun pos => YulExpr.call "calldataload" [pos]) name .uint256 (4 + 32 * idx)).length +
        rest.length + 1)
      state
      (genScalarLoad (fun pos => YulExpr.call "calldataload" [pos]) name .uint256 (4 + 32 * idx) ++ rest) =
      execIRStmts (rest.length + 1) (state.setVar name value) rest := by
  have hstmt :
      execIRStmt (rest.length + 1) state
        (YulStmt.let_ name (YulExpr.call "calldataload" [YulExpr.lit (4 + 32 * idx)])) =
        .continue (state.setVar name value) := by
      have hvalue : value = state.calldata.getD idx 0 % Compiler.Constants.evmModulus := by
        simpa [SourceSemantics.decodeSupportedParamWord, SourceSemantics.wordNormalize,
          Verity.Core.UINT256_MODULUS, uint256_modulus_eq_evm] using hdecode.symm
      cases hvalue
      simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
        Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
        Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext, calldataloadWord_aligned]
  simpa [genScalarLoad, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    execIRStmts_cons_of_execIRStmt_continue state (state.setVar name value)
      (YulStmt.let_ name (YulExpr.call "calldataload" [YulExpr.lit (4 + 32 * idx)])) rest hstmt

private theorem exec_genScalarLoad_supported_then_uint8
    (state : IRState) (rest : List YulStmt) (name : String) (idx value : Nat)
    (hdecode : SourceSemantics.decodeSupportedParamWord .uint8 (state.calldata.getD idx 0) = some value) :
    execIRStmts ((genScalarLoad (fun pos => YulExpr.call "calldataload" [pos]) name .uint8 (4 + 32 * idx)).length +
        rest.length + 1)
      state
      (genScalarLoad (fun pos => YulExpr.call "calldataload" [pos]) name .uint8 (4 + 32 * idx) ++ rest) =
      execIRStmts (rest.length + 1) (state.setVar name value) rest := by
  have hstmt :
      execIRStmt (rest.length + 1) state
        (YulStmt.let_ name
          (YulExpr.call "and" [YulExpr.call "calldataload" [YulExpr.lit (4 + 32 * idx)], YulExpr.lit 255])) =
        .continue (state.setVar name value) := by
      simp [SourceSemantics.decodeSupportedParamWord, SourceSemantics.wordNormalize,
        SourceSemantics.uint8Modulus] at hdecode
      subst value
      have h255 : (255 : Nat) % Compiler.Constants.evmModulus = 255 := by
        norm_num [Compiler.Constants.evmModulus]
      simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
        Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
        Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext, calldataloadWord_aligned, h255]
  simpa [genScalarLoad, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    execIRStmts_cons_of_execIRStmt_continue state (state.setVar name value)
      (YulStmt.let_ name
        (YulExpr.call "and" [YulExpr.call "calldataload" [YulExpr.lit (4 + 32 * idx)], YulExpr.lit 255])) rest hstmt

private theorem exec_genScalarLoad_supported_then_address
    (state : IRState) (rest : List YulStmt) (name : String) (idx value : Nat)
    (hdecode : SourceSemantics.decodeSupportedParamWord .address (state.calldata.getD idx 0) = some value) :
    execIRStmts ((genScalarLoad (fun pos => YulExpr.call "calldataload" [pos]) name .address (4 + 32 * idx)).length +
        rest.length + 1)
      state
      (genScalarLoad (fun pos => YulExpr.call "calldataload" [pos]) name .address (4 + 32 * idx) ++ rest) =
      execIRStmts (rest.length + 1) (state.setVar name value) rest := by
  have hstmt :
      execIRStmt (rest.length + 1) state
        (YulStmt.let_ name
          (YulExpr.call "and"
            [YulExpr.call "calldataload" [YulExpr.lit (4 + 32 * idx)], YulExpr.hex Compiler.Constants.addressMask])) =
        .continue (state.setVar name value) := by
      simp [SourceSemantics.decodeSupportedParamWord, SourceSemantics.wordNormalize] at hdecode
      subst value
      have hmask : Compiler.Constants.addressMask % Compiler.Constants.evmModulus =
          Compiler.Constants.addressMask := by
        have hlt : Compiler.Constants.addressMask < Compiler.Constants.evmModulus := by
          dsimp [Compiler.Constants.addressMask, Compiler.Constants.evmModulus]
          omega
        exact Nat.mod_eq_of_lt hlt
      simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
        Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
        Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext, calldataloadWord_aligned, hmask]
  simpa [genScalarLoad, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    execIRStmts_cons_of_execIRStmt_continue state (state.setVar name value)
      (YulStmt.let_ name
        (YulExpr.call "and"
          [YulExpr.call "calldataload" [YulExpr.lit (4 + 32 * idx)], YulExpr.hex Compiler.Constants.addressMask]))
      rest hstmt

private theorem exec_genScalarLoad_supported_then_bytes32
    (state : IRState) (rest : List YulStmt) (name : String) (idx value : Nat)
    (hdecode : SourceSemantics.decodeSupportedParamWord .bytes32 (state.calldata.getD idx 0) = some value) :
    execIRStmts ((genScalarLoad (fun pos => YulExpr.call "calldataload" [pos]) name .bytes32 (4 + 32 * idx)).length +
        rest.length + 1)
      state
      (genScalarLoad (fun pos => YulExpr.call "calldataload" [pos]) name .bytes32 (4 + 32 * idx) ++ rest) =
      execIRStmts (rest.length + 1) (state.setVar name value) rest := by
  have hstmt :
      execIRStmt (rest.length + 1) state
        (YulStmt.let_ name (YulExpr.call "calldataload" [YulExpr.lit (4 + 32 * idx)])) =
        .continue (state.setVar name value) := by
      have hvalue : value = state.calldata.getD idx 0 % Compiler.Constants.evmModulus := by
        simpa [SourceSemantics.decodeSupportedParamWord, SourceSemantics.wordNormalize,
          Verity.Core.UINT256_MODULUS, uint256_modulus_eq_evm] using hdecode.symm
      cases hvalue
      simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
        Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
        Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext, calldataloadWord_aligned]
  simpa [genScalarLoad, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    execIRStmts_cons_of_execIRStmt_continue state (state.setVar name value)
      (YulStmt.let_ name (YulExpr.call "calldataload" [YulExpr.lit (4 + 32 * idx)])) rest hstmt

theorem exec_genScalarLoad_supported_then
    (state : IRState) (rest : List YulStmt) (name : String) (ty : ParamType) (idx value : Nat)
    (hsupported : SupportedExternalParamType ty)
    (hdecode : SourceSemantics.decodeSupportedParamWord ty (state.calldata.getD idx 0) = some value) :
    execIRStmts ((genScalarLoad (fun pos => YulExpr.call "calldataload" [pos]) name ty (4 + 32 * idx)).length +
        rest.length + 1)
      state
      (genScalarLoad (fun pos => YulExpr.call "calldataload" [pos]) name ty (4 + 32 * idx) ++ rest) =
      execIRStmts (rest.length + 1) (state.setVar name value) rest := by
  rcases supportedExternalParamType_cases hsupported with rfl | rfl | rfl | rfl
  · exact exec_genScalarLoad_supported_then_uint256 state rest name idx value hdecode
  · exact exec_genScalarLoad_supported_then_uint8 state rest name idx value hdecode
  · exact exec_genScalarLoad_supported_then_address state rest name idx value hdecode
  · exact exec_genScalarLoad_supported_then_bytes32 state rest name idx value hdecode

theorem bindSupportedParams_names
    {params : List Param} {args : List Nat} {bindings : List (String × Nat)}
    (hbind : SourceSemantics.bindSupportedParams params args = some bindings) :
    bindings.map Prod.fst = params.map Param.name := by
  induction params generalizing args bindings with
  | nil =>
      simp [SourceSemantics.bindSupportedParams] at hbind
      cases hbind
      rfl
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
              simp [ih hrest]

theorem bindSupportedParams_names_nodup
    {params : List Param} {args : List Nat} {bindings : List (String × Nat)}
    (hparams : (params.map Param.name).Nodup)
    (hbind : SourceSemantics.bindSupportedParams params args = some bindings) :
    (bindings.map Prod.fst).Nodup := by
  rw [bindSupportedParams_names hbind]
  exact hparams

private theorem exec_minInputSizeCheck_supported_noop
    (fuel : Nat) (state : IRState) (params : List Param)
    (_hsupported : ∀ param ∈ params, SupportedExternalParamType param.ty)
    (hcalldataSizeFits : 4 + state.calldata.length * 32 < Compiler.Constants.evmModulus)
    (hlen : params.length ≤ state.calldata.length) :
    execIRStmt (Nat.succ fuel) state
      (YulStmt.if_ (YulExpr.call "lt"
        [YulExpr.call "calldatasize" [], YulExpr.lit (4 + 32 * params.length)])
        [YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]) =
      .continue state := by
  have hrhs_lt_modulus : 4 + 32 * params.length < Compiler.Constants.evmModulus := by
    omega
  have hnotlt : ¬ 4 + state.calldata.length * 32 < 4 + 32 * params.length := by
    omega
  simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext,
    Nat.mod_eq_of_lt hcalldataSizeFits, Nat.mod_eq_of_lt hrhs_lt_modulus, hnotlt]

theorem exec_genParamLoadBodyFrom_supported_then
    (state : IRState) (rest : List YulStmt) (headSize baseOffset : Nat)
    (params : List Param) (idx : Nat)
    (bindings : List (String × Nat))
    (hsupported : ∀ param ∈ params, SupportedExternalParamType param.ty)
    (hbind : SourceSemantics.bindSupportedParams params (state.calldata.drop idx) = some bindings) :
    execIRStmts ((genParamLoadBodyFrom (fun pos => YulExpr.call "calldataload" [pos])
        (YulExpr.call "calldatasize" []) headSize baseOffset params (4 + 32 * idx)).length +
        rest.length + 1)
      state
      (genParamLoadBodyFrom (fun pos => YulExpr.call "calldataload" [pos])
        (YulExpr.call "calldatasize" []) headSize baseOffset params (4 + 32 * idx) ++ rest) =
      execIRStmts (rest.length + 1) (applyBindingsToIRState state bindings) rest := by
  induction params generalizing state idx bindings rest headSize baseOffset with
  | nil =>
      simp [SourceSemantics.bindSupportedParams] at hbind
      cases hbind
      simp [Compiler.CompilationModel.genParamLoadBodyFrom, applyBindingsToIRState]
  | cons param restParams ih =>
      cases hdrop : state.calldata.drop idx with
      | nil =>
          simp [SourceSemantics.bindSupportedParams, hdrop] at hbind
      | cons arg restArgs =>
          have hparam : SupportedExternalParamType param.ty := hsupported param (by simp)
          have hrestSupported : ∀ next ∈ restParams, SupportedExternalParamType next.ty := by
            intro next hnext
            exact hsupported next (by simp [hnext])
          cases hdecode : SourceSemantics.decodeSupportedParamWord param.ty arg <;>
              simp [SourceSemantics.bindSupportedParams, hdrop, hdecode] at hbind
          case some value =>
            cases hrest : SourceSemantics.bindSupportedParams restParams restArgs <;>
                simp [hrest] at hbind
            case some restBindings =>
              cases hbind
              have hdecode' :
                  SourceSemantics.decodeSupportedParamWord param.ty (state.calldata.getD idx 0) =
                    some value := by
                have hget : state.calldata.getD idx 0 = arg := getD_eq_of_drop_eq_cons hdrop
                rw [hget]
                exact hdecode
              have htail :
                  (state.setVar param.name value).calldata.drop (idx + 1) = restArgs := by
                simpa [IRState.setVar] using drop_succ_eq_of_drop_eq_cons hdrop
              rcases supportedExternalParamType_cases hparam with hty | hty | hty | hty
              ·
                have hdecode_uint256 :
                    SourceSemantics.decodeSupportedParamWord .uint256 (state.calldata.getD idx 0) =
                      some value := by
                  simpa [hty] using hdecode'
                have hoff : 4 + 32 * (idx + 1) = 4 + (32 + 32 * idx) := by omega
                simpa [Compiler.CompilationModel.genParamLoadBodyFrom, paramHeadSize, IRState.setVar,
                  Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, applyBindingsToIRState, hty, hoff] using
                  (exec_genScalarLoad_supported_then (state := state)
                    (rest := genParamLoadBodyFrom (fun pos => YulExpr.call "calldataload" [pos])
                      (YulExpr.call "calldatasize" []) headSize baseOffset restParams
                      (4 + 32 * (idx + 1)) ++ rest)
                    (name := param.name) (ty := .uint256) (idx := idx) (value := value)
                    (hsupported := trivial) (hdecode := hdecode_uint256)).trans
                    (by
                      simpa [IRState.setVar, htail, applyBindingsToIRState, paramHeadSize,
                        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                        ih (state := state.setVar param.name value) (headSize := headSize)
                          (baseOffset := baseOffset) (idx := idx + 1)
                          (bindings := restBindings) (rest := rest) hrestSupported
                          (by simpa [htail] using hrest))
              ·
                have hdecode_uint8 :
                    SourceSemantics.decodeSupportedParamWord .uint8 (state.calldata.getD idx 0) =
                      some value := by
                  simpa [hty] using hdecode'
                have hoff : 4 + 32 * (idx + 1) = 4 + (32 + 32 * idx) := by omega
                simpa [Compiler.CompilationModel.genParamLoadBodyFrom, paramHeadSize, IRState.setVar,
                  Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, applyBindingsToIRState, hty, hoff] using
                  (exec_genScalarLoad_supported_then (state := state)
                    (rest := genParamLoadBodyFrom (fun pos => YulExpr.call "calldataload" [pos])
                      (YulExpr.call "calldatasize" []) headSize baseOffset restParams
                      (4 + 32 * (idx + 1)) ++ rest)
                    (name := param.name) (ty := .uint8) (idx := idx) (value := value)
                    (hsupported := trivial) (hdecode := hdecode_uint8)).trans
                    (by
                      simpa [IRState.setVar, htail, applyBindingsToIRState, paramHeadSize,
                        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                        ih (state := state.setVar param.name value) (headSize := headSize)
                          (baseOffset := baseOffset) (idx := idx + 1)
                          (bindings := restBindings) (rest := rest) hrestSupported
                          (by simpa [htail] using hrest))
              ·
                have hdecode_address :
                    SourceSemantics.decodeSupportedParamWord .address (state.calldata.getD idx 0) =
                      some value := by
                  simpa [hty] using hdecode'
                have hoff : 4 + 32 * (idx + 1) = 4 + (32 + 32 * idx) := by omega
                simpa [Compiler.CompilationModel.genParamLoadBodyFrom, paramHeadSize, IRState.setVar,
                  Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, applyBindingsToIRState, hty, hoff] using
                  (exec_genScalarLoad_supported_then (state := state)
                    (rest := genParamLoadBodyFrom (fun pos => YulExpr.call "calldataload" [pos])
                      (YulExpr.call "calldatasize" []) headSize baseOffset restParams
                      (4 + 32 * (idx + 1)) ++ rest)
                    (name := param.name) (ty := .address) (idx := idx) (value := value)
                    (hsupported := trivial) (hdecode := hdecode_address)).trans
                    (by
                      simpa [IRState.setVar, htail, applyBindingsToIRState, paramHeadSize,
                        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                        ih (state := state.setVar param.name value) (headSize := headSize)
                          (baseOffset := baseOffset) (idx := idx + 1)
                          (bindings := restBindings) (rest := rest) hrestSupported
                          (by simpa [htail] using hrest))
              ·
                have hdecode_bytes32 :
                    SourceSemantics.decodeSupportedParamWord .bytes32 (state.calldata.getD idx 0) =
                      some value := by
                  simpa [hty] using hdecode'
                have hoff : 4 + 32 * (idx + 1) = 4 + (32 + 32 * idx) := by omega
                simpa [Compiler.CompilationModel.genParamLoadBodyFrom, paramHeadSize, IRState.setVar,
                  Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, applyBindingsToIRState, hty, hoff] using
                  (exec_genScalarLoad_supported_then (state := state)
                    (rest := genParamLoadBodyFrom (fun pos => YulExpr.call "calldataload" [pos])
                      (YulExpr.call "calldatasize" []) headSize baseOffset restParams
                      (4 + 32 * (idx + 1)) ++ rest)
                    (name := param.name) (ty := .bytes32) (idx := idx) (value := value)
                    (hsupported := trivial) (hdecode := hdecode_bytes32)).trans
                    (by
                      simpa [IRState.setVar, htail, applyBindingsToIRState, paramHeadSize,
                        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                        ih (state := state.setVar param.name value) (headSize := headSize)
                          (baseOffset := baseOffset) (idx := idx + 1)
                          (bindings := restBindings) (rest := rest) hrestSupported
                          (by simpa [htail] using hrest))

theorem exec_genParamLoads_supported
    (state : IRState) (params : List Param) (bindings : List (String × Nat))
    (hsupported : ∀ param ∈ params, SupportedExternalParamType param.ty)
    (hcalldataSizeFits : 4 + state.calldata.length * 32 < Compiler.Constants.evmModulus)
    (hbind : SourceSemantics.bindSupportedParams params state.calldata = some bindings) :
    execIRStmts ((genParamLoads params).length + 1) state (genParamLoads params) =
      .continue (applyBindingsToIRState state bindings) := by
  have hlen : params.length ≤ state.calldata.length := bindSupportedParams_some_length hbind
  let body :=
    genParamLoadBodyFrom (fun pos => YulExpr.call "calldataload" [pos])
      (YulExpr.call "calldatasize" []) (32 * params.length) 4 params 4
  have hguard :
      execIRStmt (body.length + 1) state
        (YulStmt.if_ (YulExpr.call "lt"
          [YulExpr.call "calldatasize" [], YulExpr.lit (4 + 32 * params.length)])
          [YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]) =
        .continue state :=
    exec_minInputSizeCheck_supported_noop (fuel := body.length) state params hsupported
      hcalldataSizeFits hlen
  have hbody :=
    exec_genParamLoadBodyFrom_supported_then (state := state) (rest := []) (headSize := 32 * params.length)
      (baseOffset := 4) (params := params) (idx := 0) (bindings := bindings) hsupported
      (by simpa using hbind)
  have hstep :=
    execIRStmts_cons_of_execIRStmt_continue state state
      (YulStmt.if_ (YulExpr.call "lt"
        [YulExpr.call "calldatasize" [], YulExpr.lit (4 + 32 * params.length)])
        [YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])])
      body hguard
  have hbody' :
      execIRStmts (body.length + 1) state body =
        .continue (applyBindingsToIRState state bindings) := by
    simpa [body] using hbody
  simpa [Compiler.CompilationModel.genParamLoads, Compiler.CompilationModel.genParamLoadsFrom,
    body, supportedScalarHeadSize_eq params hsupported] using hstep.trans hbody'

theorem exec_genParamLoads_supported_then
    (state : IRState) (params : List Param) (bindings : List (String × Nat))
    (rest : List YulStmt)
    (hsupported : ∀ param ∈ params, SupportedExternalParamType param.ty)
    (hcalldataSizeFits : 4 + state.calldata.length * 32 < Compiler.Constants.evmModulus)
    (hbind : SourceSemantics.bindSupportedParams params state.calldata = some bindings) :
    execIRStmts ((genParamLoads params).length + rest.length + 1) state (genParamLoads params ++ rest) =
      execIRStmts (rest.length + 1) (applyBindingsToIRState state bindings) rest := by
  let body :=
    genParamLoadBodyFrom (fun pos => YulExpr.call "calldataload" [pos])
      (YulExpr.call "calldatasize" []) (32 * params.length) 4 params 4
  have hlen : params.length ≤ state.calldata.length := bindSupportedParams_some_length hbind
  have hguard :
      execIRStmt (body.length + rest.length + 1) state
        (YulStmt.if_ (YulExpr.call "lt"
          [YulExpr.call "calldatasize" [], YulExpr.lit (4 + 32 * params.length)])
          [YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]) =
        .continue state :=
    exec_minInputSizeCheck_supported_noop (fuel := body.length + rest.length) state params hsupported
      hcalldataSizeFits hlen
  have hbody :=
    exec_genParamLoadBodyFrom_supported_then (state := state) (rest := rest) (headSize := 32 * params.length)
      (baseOffset := 4) (params := params) (idx := 0) (bindings := bindings) hsupported
      (by simpa using hbind)
  have hstep :=
    execIRStmts_cons_of_execIRStmt_continue state state
      (YulStmt.if_ (YulExpr.call "lt"
        [YulExpr.call "calldatasize" [], YulExpr.lit (4 + 32 * params.length)])
        [YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])])
      (body ++ rest) (by simpa [body] using hguard)
  have hbody' :
      execIRStmts ((body ++ rest).length + 1) state (body ++ rest) =
        execIRStmts (rest.length + 1) (applyBindingsToIRState state bindings) rest := by
    simpa [body] using hbody
  have hfuel :
      rest.length + (2 + body.length) = rest.length + (1 + (1 + body.length)) := by
    omega
  have hstep' :
      execIRStmts ((genParamLoads params).length + rest.length + 1) state (genParamLoads params ++ rest) =
        execIRStmts ((body ++ rest).length + 1) state (body ++ rest) := by
    simpa [Compiler.CompilationModel.genParamLoads, Compiler.CompilationModel.genParamLoadsFrom,
      body, List.length_append, supportedScalarHeadSize_eq params hsupported, hfuel,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep
  calc
    execIRStmts ((genParamLoads params).length + rest.length + 1) state (genParamLoads params ++ rest)
        = execIRStmts ((body ++ rest).length + 1) state (body ++ rest) := hstep'
    _ = execIRStmts (rest.length + 1) (applyBindingsToIRState state bindings) rest := hbody'

end ParamLoading

end Compiler.Proofs.IRGeneration
