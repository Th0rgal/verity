import Compiler.Specs
import Compiler.Selector
import Compiler.ContractSpec
import Compiler.Codegen
import Compiler.Gas.StaticAnalysis

namespace Compiler.Gas

open Compiler
open Compiler.ContractSpec
open Compiler.Selector

private structure CliConfig where
  loopIterations : Nat := 8
  unknownCallCost : Nat := 50000
  unknownForwardedGas : Nat := 50000
  fuel : Nat := 4096
  patchEnabled : Bool := false
  patchMaxIterations : Nat := 2

private def parseNatFlag (flag : String) (raw : String) : IO Nat :=
  match raw.toNat? with
  | some n => pure n
  | none => throw <| IO.userError s!"Invalid Nat for {flag}: {raw}"

private def printHelp : IO Unit := do
  IO.println "Static gas upper-bound report for Verity contracts"
  IO.println ""
  IO.println "Usage: lake exe gas-report [options]"
  IO.println ""
  IO.println "Options:"
  IO.println "  --loop-iterations <n>   Loop upper bound used by static analysis (default: 8)"
  IO.println "  --unknown-call-cost <n> Fallback cost for unknown builtins/calls (default: 50000)"
  IO.println "  --unknown-forwarded-gas <n> Fallback forwarded gas for CALL-like builtins (default: 50000)"
  IO.println "  --fuel <n>              Structural recursion fuel for analysis (default: 4096)"
  IO.println "  --enable-patches        Enable deterministic Yul patch pass before gas analysis"
  IO.println "  --patch-max-iterations <n>  Max patch-pass fixpoint iterations (default: 2)"
  IO.println "  --help                  Show this help message"

private def parseArgs (args : List String) : IO CliConfig := do
  let rec go (rest : List String) (cfg : CliConfig) : IO CliConfig := do
    match rest with
    | [] => pure cfg
    | "--help" :: _ =>
        printHelp
        throw <| IO.userError "help"
    | "--loop-iterations" :: value :: tail =>
        go tail { cfg with loopIterations := (← parseNatFlag "--loop-iterations" value) }
    | "--unknown-call-cost" :: value :: tail =>
        go tail { cfg with unknownCallCost := (← parseNatFlag "--unknown-call-cost" value) }
    | "--unknown-forwarded-gas" :: value :: tail =>
        go tail { cfg with unknownForwardedGas := (← parseNatFlag "--unknown-forwarded-gas" value) }
    | "--fuel" :: value :: tail =>
        go tail { cfg with fuel := (← parseNatFlag "--fuel" value) }
    | "--enable-patches" :: tail =>
        go tail { cfg with patchEnabled := true }
    | "--patch-max-iterations" :: value :: tail =>
        go tail {
          cfg with
            patchEnabled := true
            patchMaxIterations := (← parseNatFlag "--patch-max-iterations" value)
        }
    | flag :: _ =>
        throw <| IO.userError s!"Unknown argument: {flag}. Use --help for usage."
  go args {}

private def compileAndBound
    (cfg : GasConfig)
    (fuel : Nat)
    (emitOptions : Compiler.YulEmitOptions)
    (spec : ContractSpec) : IO (String × Nat × Nat) := do
  let selectors ← computeSelectors spec
  match Compiler.ContractSpec.compile spec selectors with
  | .error err => throw <| IO.userError s!"Failed to compile {spec.name}: {err}"
  | .ok irContract =>
      let yulObj := Compiler.emitYulWithOptions irContract emitOptions
      let deployBound := stmtsUpperBound cfg fuel yulObj.deployCode
      let runtimeBound := stmtsUpperBound cfg fuel yulObj.runtimeCode
      pure (spec.name, deployBound, runtimeBound)

private def printRow (name : String) (deploy runtime : Nat) : IO Unit :=
  IO.println s!"{name}\t{deploy}\t{runtime}\t{deploy + runtime}"

def main (args : List String) : IO Unit := do
  try
    let cli ← parseArgs args
    let gasCfg : GasConfig := {
      loopIterations := cli.loopIterations
      unknownCallCost := cli.unknownCallCost
      unknownForwardedGas := cli.unknownForwardedGas
    }
    let emitOptions : Compiler.YulEmitOptions := {
      patchConfig := {
        enabled := cli.patchEnabled
        maxIterations := cli.patchMaxIterations
      }
    }

    IO.println s!"# gas-report loopIterations={cli.loopIterations} unknownCallCost={cli.unknownCallCost} unknownForwardedGas={cli.unknownForwardedGas} fuel={cli.fuel} patchEnabled={cli.patchEnabled} patchMaxIterations={cli.patchMaxIterations}"
    IO.println "contract\tdeploy_upper_bound\truntime_upper_bound\ttotal_upper_bound"

    let mut totalDeploy := 0
    let mut totalRuntime := 0

    for spec in Compiler.Specs.allSpecs do
      let (name, deployBound, runtimeBound) ← compileAndBound gasCfg cli.fuel emitOptions spec
      totalDeploy := totalDeploy + deployBound
      totalRuntime := totalRuntime + runtimeBound
      printRow name deployBound runtimeBound

    IO.println s!"TOTAL\t{totalDeploy}\t{totalRuntime}\t{totalDeploy + totalRuntime}"
  catch e =>
    if e.toString == "help" then
      pure ()
    else
      throw e

end Compiler.Gas

def main (args : List String) : IO Unit :=
  Compiler.Gas.main args
