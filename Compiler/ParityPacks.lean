import Compiler.Codegen
import Compiler.Yul.PatchRules
import Lean

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
  compositionProofRef : Lean.Name
  /-- Activation-time proof registry used by this pack's rewrite policy. -/
  requiredProofRefs : List Lean.Name
  deriving Repr, DecidableEq

private def isDeduped (xs : List Lean.Name) : Bool :=
  let rec go (seen : List Lean.Name) : List Lean.Name → Bool
    | [] => true
    | x :: rest =>
        if seen.any (fun prior => prior = x) then
          false
        else
          go (x :: seen) rest
  go [] xs

private def containsAll (superset subset : List Lean.Name) : Bool :=
  subset.all (fun item => superset.any (fun present => present = item))

/-- Fail-closed pack-level proof composition check for the selected rewrite bundle. -/
def ParityPack.proofCompositionValid (pack : ParityPack) : Bool :=
  match Compiler.Yul.findRewriteBundle? pack.rewriteBundleId with
  | none => false
  | some _ =>
      pack.compositionProofRef != .anonymous &&
        !(pack.requiredProofRefs.isEmpty) &&
        pack.requiredProofRefs.all (fun ref => ref != .anonymous) &&
        isDeduped pack.requiredProofRefs &&
        containsAll pack.requiredProofRefs (Compiler.Yul.rewriteProofAllowlistForId pack.rewriteBundleId)

/-- Registry of all shipped parity packs.
    External contract packs (e.g. Morpho) register their packs via plugin imports. -/
def allParityPacks : List ParityPack :=
  []

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
