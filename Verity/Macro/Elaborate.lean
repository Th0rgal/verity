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
  let (contractName, fields, errorDecls, constDecls, immutableDecls, externalDecls, ctor, functions) ← parseContractSyntax stx

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

    for fn in functions do
      let fnCmds ← mkFunctionCommandsPublic fields constDecls immutableDecls functions fn
      for cmd in fnCmds do
        elabCommand cmd
      elabCommand (← mkBridgeCommand fn.ident)

    elabCommand (← mkSpecCommandPublic (toString contractName.getId) fields errorDecls constDecls immutableDecls externalDecls ctor functions)

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

    -- Emit per-function _modifies theorem and _frame definition for
    -- functions with modifies(...) annotation (#1729, Axis 3 Step 1b).
    for fn in functions do
      if !fn.modifies.isEmpty then
        elabCommand (← mkModifiesTheoremCommand fn)
        let frameCmds ← mkFrameDefCommand fields fn
        for cmd in frameCmds do
          elabCommand cmd

    elabCommand (← `(end $contractName))
  catch err =>
    elabCommand (← `(end $contractName))
    throw err

end Verity.Macro
