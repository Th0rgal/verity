import Lean
import Compiler.CompilationModel
import Compiler.Selector
import Verity.Macro.Syntax

namespace Verity.Macro

open Lean
open Lean.Elab
open Lean.Elab.Command

private def formatCompileError (contractName : Name) (err : String) : String :=
  s!"#check_contract failed for '{contractName}': {err}"

@[command_elab checkContractCmd]
def elabCheckContract : CommandElab := fun stx => do
  match stx with
  | `(#check_contract $contract:ident) => do
      let env ← getEnv
      let opts ← getOptions
      let currentNs ← getCurrNamespace
      let rawName := contract.getId
      let contractCandidates : List Name :=
        if currentNs == Name.anonymous then
          [rawName]
        else
          [rawName, currentNs ++ rawName]
      let mut resolvedContractName : Option Name := none
      let mut resolvedSpec : Option Compiler.CompilationModel.CompilationModel := none
      for contractName in contractCandidates do
        let specName := contractName ++ `spec
        if env.contains specName then
          match unsafe env.evalConstCheck Compiler.CompilationModel.CompilationModel opts
              ``Compiler.CompilationModel.CompilationModel specName with
          | .ok spec =>
              resolvedContractName := some contractName
              resolvedSpec := some spec
              break
          | .error _ => pure ()
      let contractName ←
        match resolvedContractName with
        | some name => pure name
        | none =>
            throwErrorAt contract s!"#check_contract expected a generated '<Contract>.spec' CompilationModel for '{contract.getId}'"
      let spec ←
        match resolvedSpec with
        | some spec => pure spec
        | none =>
            throwErrorAt contract s!"#check_contract expected a generated '<Contract>.spec' CompilationModel for '{contract.getId}'"
      let selectors ← liftIO <| Compiler.Selector.computeSelectors spec
      match Compiler.CompilationModel.compile spec selectors with
      | .ok _ =>
          logInfo m!"#check_contract ok: {contractName}"
      | .error err =>
          throwErrorAt contract (formatCompileError contractName err)
  | _ => throwErrorAt stx "invalid #check_contract command"

end Verity.Macro
