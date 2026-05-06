import Benchmark.Cases.Polygon.AgglayerBridge.Contract

namespace Benchmark.Cases.Polygon.AgglayerBridge

open Verity
open Verity.EVM.Uint256

/-! Minimal success-state specs for the AgglayerBridge Merkle/nullifier invariant. -/

def calculateGlobalExitRoot_spec (mainnetExitRoot rollupExitRoot : Uint256) : Uint256 :=
  xor mainnetExitRoot rollupExitRoot

def calculateRoot_spec (leafHash : Uint256) (proof : Array Uint256) (index : Uint256) : Uint256 :=
  let proofHead := proof.getD 0 0
  xor (xor leafHash index) proofHead

def getLeafValue_spec
    (leafType originNetwork : Uint256)
    (originAddress destinationAddress : Address)
    (destinationNetwork amount metadataHash : Uint256) : Uint256 :=
  xor
    (xor (xor leafType originNetwork) originAddress.toNat)
    (xor (xor destinationNetwork destinationAddress.toNat) (xor amount metadataHash))

def _validateAndDecodeGlobalIndex_leafIndex (globalIndex : Uint256) : Uint256 :=
  and globalIndex LOW_32_MASK

def _validateAndDecodeGlobalIndex_indexRollup (globalIndex : Uint256) : Uint256 :=
  if and globalIndex GLOBAL_INDEX_MAINNET_FLAG != 0 then 0 else shr 32 globalIndex

def _validateAndDecodeGlobalIndex_sourceBridgeNetwork (globalIndex : Uint256) : Uint256 :=
  if and globalIndex GLOBAL_INDEX_MAINNET_FLAG != 0 then 0 else add (shr 32 globalIndex) 1

def _validateAndDecodeGlobalIndex_valid (globalIndex : Uint256) : Prop :=
  let leafIndex := _validateAndDecodeGlobalIndex_leafIndex globalIndex
  if and globalIndex GLOBAL_INDEX_MAINNET_FLAG != 0 then
    add GLOBAL_INDEX_MAINNET_FLAG leafIndex = globalIndex
  else
    add (shl 32 (_validateAndDecodeGlobalIndex_indexRollup globalIndex)) leafIndex = globalIndex

def _bitmapPositions_wordPos (index : Uint256) : Uint256 := shr 8 index
def _bitmapPositions_bitPos (index : Uint256) : Uint256 := and index LOW_8_MASK
def _bitmapPositions_mask (index : Uint256) : Uint256 := shl (_bitmapPositions_bitPos index) 1

def nullifierGlobalIndex (networkID leafIndex sourceBridgeNetwork : Uint256) : Uint256 :=
  globalIndexForNullifierModel networkID leafIndex sourceBridgeNetwork

def claimedWord (s : ContractState) (wordPos : Uint256) : Uint256 :=
  s.storageMapUint 4 wordPos

def isClaimed_spec (s : ContractState) (networkID leafIndex sourceBridgeNetwork : Uint256) : Prop :=
  let nullifierIndex := nullifierGlobalIndex networkID leafIndex sourceBridgeNetwork
  let mask := _bitmapPositions_mask nullifierIndex
  and (claimedWord s (_bitmapPositions_wordPos nullifierIndex)) mask = mask

def validClaimLeaf_spec
    (s : ContractState)
    (smtProofLocalExitRoot smtProofRollupExitRoot : Array Uint256)
    (globalIndex mainnetExitRoot rollupExitRoot leafValue : Uint256) : Prop :=
  let globalExitRoot := calculateGlobalExitRoot_spec mainnetExitRoot rollupExitRoot
  let leafIndex := _validateAndDecodeGlobalIndex_leafIndex globalIndex
  let indexRollup := _validateAndDecodeGlobalIndex_indexRollup globalIndex
  s.storageMapUint 3 globalExitRoot != 0 ∧
  _validateAndDecodeGlobalIndex_valid globalIndex ∧
  if and globalIndex GLOBAL_INDEX_MAINNET_FLAG != 0 then
    calculateRoot_spec leafValue smtProofLocalExitRoot leafIndex = mainnetExitRoot
  else
    calculateRoot_spec
      (calculateRoot_spec leafValue smtProofLocalExitRoot leafIndex)
      smtProofRollupExitRoot
      indexRollup = rollupExitRoot

/--
Every successful `claimAsset` has a valid accepted Merkle leaf and leaves the
corresponding `(sourceBridgeNetwork, leafIndex)` nullifier claimed.
-/
def claimAsset_valid_leaf_and_consumes_unique_nullifier_spec
    (s s' : ContractState)
    (smtProofLocalExitRoot smtProofRollupExitRoot : Array Uint256)
    (globalIndex mainnetExitRoot rollupExitRoot originNetwork : Uint256)
    (originTokenAddress : Address)
    (destinationNetwork : Uint256)
    (destinationAddress : Address)
    (amount metadataHash : Uint256) : Prop :=
  let leafIndex := _validateAndDecodeGlobalIndex_leafIndex globalIndex
  let sourceBridgeNetwork := _validateAndDecodeGlobalIndex_sourceBridgeNetwork globalIndex
  let leafValue := getLeafValue_spec LEAF_TYPE_ASSET originNetwork originTokenAddress destinationAddress destinationNetwork amount metadataHash
  destinationNetwork = s.storage 2 ∧
  validClaimLeaf_spec s smtProofLocalExitRoot smtProofRollupExitRoot globalIndex mainnetExitRoot rollupExitRoot leafValue ∧
  ¬ isClaimed_spec s (s.storage 2) leafIndex sourceBridgeNetwork ∧
  isClaimed_spec s' (s.storage 2) leafIndex sourceBridgeNetwork

/--
Every successful `claimMessage` has a valid accepted Merkle leaf and leaves the
corresponding `(sourceBridgeNetwork, leafIndex)` nullifier claimed.
-/
def claimMessage_valid_leaf_and_consumes_unique_nullifier_spec
    (s s' : ContractState)
    (smtProofLocalExitRoot smtProofRollupExitRoot : Array Uint256)
    (globalIndex mainnetExitRoot rollupExitRoot originNetwork : Uint256)
    (originAddress : Address)
    (destinationNetwork : Uint256)
    (destinationAddress : Address)
    (amount metadataHash : Uint256) : Prop :=
  let leafIndex := _validateAndDecodeGlobalIndex_leafIndex globalIndex
  let sourceBridgeNetwork := _validateAndDecodeGlobalIndex_sourceBridgeNetwork globalIndex
  let leafValue := getLeafValue_spec LEAF_TYPE_MESSAGE originNetwork originAddress destinationAddress destinationNetwork amount metadataHash
  destinationNetwork = s.storage 2 ∧
  validClaimLeaf_spec s smtProofLocalExitRoot smtProofRollupExitRoot globalIndex mainnetExitRoot rollupExitRoot leafValue ∧
  ¬ isClaimed_spec s (s.storage 2) leafIndex sourceBridgeNetwork ∧
  isClaimed_spec s' (s.storage 2) leafIndex sourceBridgeNetwork

end Benchmark.Cases.Polygon.AgglayerBridge
