import Compiler.Codegen
import Compiler.Yul.PatchRules

namespace Compiler

/-- Pinned Solidity tuple metadata for one parity pack. -/
structure ParityTargetTuple where
  solcVersion : String
  solcCommit : String
  optimizerRuns : Nat
  viaIR : Bool
  evmVersion : String
  metadataMode : String
  deriving Repr, DecidableEq

/-- Versioned parity-pack selection unit. -/
structure ParityPack where
  id : String
  compat : ParityTargetTuple
  backendProfile : BackendProfile
  forcePatches : Bool
  defaultPatchMaxIterations : Nat
  /-- Rewrite bundle ID selected for this parity tuple. -/
  rewriteBundleId : String
  /-- Pack-level composition theorem for the active rewrite set. -/
  compositionProofRef : String
  /-- Activation-time proof registry used by this pack's rewrite policy. -/
  requiredProofRefs : List String
  deriving Repr, DecidableEq

private def isDeduped (xs : List String) : Bool :=
  let rec go (seen : List String) : List String → Bool
    | [] => true
    | x :: rest =>
        if seen.any (fun prior => prior = x) then
          false
        else
          go (x :: seen) rest
  go [] xs

private def containsAll (superset subset : List String) : Bool :=
  subset.all (fun item => superset.any (fun present => present = item))

/-- Fail-closed pack-level proof composition check for the selected rewrite bundle. -/
def ParityPack.proofCompositionValid (pack : ParityPack) : Bool :=
  match Compiler.Yul.findRewriteBundle? pack.rewriteBundleId with
  | none => false
  | some _ =>
      !(pack.compositionProofRef.isEmpty) &&
        !(pack.requiredProofRefs.isEmpty) &&
        pack.requiredProofRefs.all (fun ref => !(ref.isEmpty)) &&
        isDeduped pack.requiredProofRefs &&
        containsAll pack.requiredProofRefs (Compiler.Yul.rewriteProofAllowlistForId pack.rewriteBundleId)

def solc_0_8_28_o200_viair_false_evm_shanghai : ParityPack :=
  { id := "solc-0.8.28-o200-viair-false-evm-shanghai"
    compat := {
      solcVersion := "0.8.28"
      solcCommit := "7893614a"
      optimizerRuns := 200
      viaIR := false
      evmVersion := "shanghai"
      metadataMode := "default"
    }
    backendProfile := .solidityParity
    forcePatches := true
    defaultPatchMaxIterations := 6
    rewriteBundleId := Compiler.Yul.solcCompatRewriteBundleId
    compositionProofRef := "Compiler.Proofs.YulGeneration.PatchRulesProofs.foundation_patch_pack_obligations"
    requiredProofRefs := Compiler.Yul.solcCompatProofAllowlist
  }

def solc_0_8_33_o200_viair_false_evm_shanghai : ParityPack :=
  { id := "solc-0.8.33-o200-viair-false-evm-shanghai"
    compat := {
      solcVersion := "0.8.33"
      solcCommit := "64118f21"
      optimizerRuns := 200
      viaIR := false
      evmVersion := "shanghai"
      metadataMode := "default"
    }
    backendProfile := .solidityParity
    forcePatches := true
    defaultPatchMaxIterations := 6
    rewriteBundleId := Compiler.Yul.solcCompatRewriteBundleId
    compositionProofRef := "Compiler.Proofs.YulGeneration.PatchRulesProofs.foundation_patch_pack_obligations"
    requiredProofRefs := Compiler.Yul.solcCompatProofAllowlist
  }

def solc_0_8_28_o999999_viair_true_evm_paris : ParityPack :=
  { id := "solc-0.8.28-o999999-viair-true-evm-paris"
    compat := {
      solcVersion := "0.8.28"
      solcCommit := "7893614a"
      optimizerRuns := 999999
      viaIR := true
      evmVersion := "paris"
      metadataMode := "none"
    }
    backendProfile := .solidityParity
    forcePatches := true
    defaultPatchMaxIterations := 6
    rewriteBundleId := Compiler.Yul.solcCompatRewriteBundleId
    compositionProofRef := "Compiler.Proofs.YulGeneration.PatchRulesProofs.foundation_patch_pack_obligations"
    requiredProofRefs := Compiler.Yul.solcCompatProofAllowlist
  }

def allParityPacks : List ParityPack :=
  [solc_0_8_33_o200_viair_false_evm_shanghai,
   solc_0_8_28_o200_viair_false_evm_shanghai,
   solc_0_8_28_o999999_viair_true_evm_paris]

def supportedParityPackIds : List String :=
  allParityPacks.map (·.id)

def findParityPack? (packId : String) : Option ParityPack :=
  allParityPacks.find? (fun pack => pack.id = packId)

/-- Registry invariant: shipped parity packs must carry valid composition-proof metadata. -/
def allParityPacksProofCompositionValid : Bool :=
  allParityPacks.all (fun pack => pack.proofCompositionValid)

example : allParityPacksProofCompositionValid = true := by
  native_decide

end Compiler
