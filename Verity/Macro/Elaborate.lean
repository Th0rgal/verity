import Lean
import Verity.Macro.Syntax
import Verity.Macro.Translate
import Verity.Macro.Bridge

namespace Verity.Macro

open Lean
open Lean.Elab
open Lean.Elab.Command

set_option hygiene false

@[command_elab verityContractCmd]
def elabVerityContract : CommandElab := fun stx => do
  let (contractName, _newtypeDecls, adtDecls, fields, errorDecls, constDecls, immutableDecls, externalDecls, ctor, functions, storageNamespace) ← parseContractSyntax stx

  validateGeneratedDefNamesPublic fields constDecls functions
  validateConstantDeclsPublic constDecls
  validateImmutableDeclsPublic fields constDecls immutableDecls ctor
  validateExternalDeclsPublic externalDecls
  validateFunctionDeclsPublic fields errorDecls constDecls immutableDecls externalDecls ctor functions

  elabCommand (← `(namespace $contractName))
  try
    for constant in constDecls do
      elabCommand (← mkConstantDefCommandPublic constant)

    for field in fields do
      elabCommand (← mkStorageDefCommandPublic field)

    for imm in immutableDecls.zipIdx do
      elabCommand (← mkStorageDefCommandPublic (immutableStorageFieldDecl fields imm.1 imm.2))

    -- Emit storageNamespace : Nat for the contract (#1730, Axis 4 Step 4a).
    -- Use the resolved namespace from parseContractSyntax to respect custom keys.
    elabCommand (← mkStorageNamespaceCommand (toString contractName.getId) storageNamespace)

    for fn in functions do
      let fnCmds ← mkFunctionCommandsPublic fields constDecls immutableDecls externalDecls functions fn
      for cmd in fnCmds do
        elabCommand cmd
      elabCommand (← mkBridgeCommand fn.ident)

    elabCommand (← mkSpecCommandPublic (toString contractName.getId) fields errorDecls constDecls immutableDecls externalDecls ctor functions adtDecls storageNamespace)

    let findIdxSimpCmds ← mkFindIdxFieldSimpCommandsPublic contractName fields
    for cmd in findIdxSimpCmds do
      elabCommand cmd

    let findIdxParamSimpCmds ← mkFindIdxParamSimpCommandsPublic contractName ctor functions
    for cmd in findIdxParamSimpCmds do
      elabCommand cmd

    -- Emit per-function semantic preservation theorem skeletons after spec generation.
    for fn in functions do
      elabCommand (← mkSemanticBridgeCommand contractName fields fn)

    -- Emit per-function _is_view theorems for view functions (#1729, Axis 3 Step 1a).
    for fn in functions do
      if fn.isView then
        elabCommand (← mkViewTheoremCommand fn)

    -- Emit per-function _no_calls theorems for no_external_calls functions (#1729, Axis 3 Step 1c).
    for fn in functions do
      if fn.noExternalCalls then
        elabCommand (← mkNoCallsTheoremCommand fn)

    -- Emit per-function _modifies theorem and _frame definition for
    -- functions with modifies(...) annotation (#1729, Axis 3 Step 1b).
    for fn in functions do
      if !fn.modifies.isEmpty then
        elabCommand (← mkModifiesTheoremCommand fn)
        let frameCmds ← mkFrameDefCommand fields fn
        for cmd in frameCmds do
          elabCommand cmd

    -- Emit per-function _effects conjunction theorem when multiple effect
    -- annotations are active on the same function (#1729, Axis 3 Step 1d).
    for fn in functions do
      if effectAnnotationCount fn ≥ 2 then
        elabCommand (← mkEffectsTheoremCommand fn)

    -- Emit per-function _cei_compliant theorem for functions that use default
    -- CEI enforcement (rung 1) — i.e. not opted out via any escalation rung.
    -- (#1728, Axis 2 Step 2a)
    for fn in functions do
      if !fn.allowPostInteractionWrites && fn.nonReentrantLock.isNone && !fn.ceiSafe then
        elabCommand (← mkCEICompliantTheoremCommand fn)

    -- Emit per-function _nonreentrant theorem for functions with nonreentrant(field).
    -- (#1728, Axis 2 Step 2b — known-safe guard rung)
    for fn in functions do
      match fn.nonReentrantLock with
      | some lockIdent =>
          elabCommand (← mkNonReentrantTheoremCommand fn (toString lockIdent.getId))
      | none => pure ()

    -- Emit per-function _cei_safe theorem for functions with cei_safe annotation.
    -- (#1728, Axis 2 Step 2b — Lean proof rung)
    for fn in functions do
      if fn.ceiSafe then
        elabCommand (← mkCEISafeTheoremCommand fn)

    -- Emit per-function _requires_role theorem for functions with requires(field).
    -- (#1728, Axis 2 Step 2c — access control)
    for fn in functions do
      match fn.requiresRole with
      | some roleIdent =>
          elabCommand (← mkRequiresRoleTheoremCommand fn (toString roleIdent.getId))
      | none => pure ()

    elabCommand (← `(end $contractName))
  catch err =>
    elabCommand (← `(end $contractName))
    throw err

end Verity.Macro
