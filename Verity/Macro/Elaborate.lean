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
  let (contractName, fields, ctor, functions) ← parseContractSyntax stx

  elabCommand (← `(namespace $contractName))

  for field in fields do
    elabCommand (← mkStorageDefCommandPublic field)

  for fn in functions do
    let fnCmds ← mkFunctionCommandsPublic fields fn
    for cmd in fnCmds do
      elabCommand cmd
    elabCommand (← mkBridgeCommand fn.ident)

  elabCommand (← mkSpecCommandPublic (toString contractName.getId) fields ctor functions)

  let findIdxSimpCmds ← mkFindIdxFieldSimpCommandsPublic contractName fields
  for cmd in findIdxSimpCmds do
    elabCommand cmd

  -- Emit per-function semantic preservation theorem skeletons after spec generation.
  for fn in functions do
    elabCommand (← mkSemanticBridgeCommand contractName fields fn)

  elabCommand (← `(end $contractName))

end Verity.Macro
