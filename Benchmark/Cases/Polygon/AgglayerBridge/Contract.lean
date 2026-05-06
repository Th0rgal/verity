import Contracts.Common

namespace Benchmark.Cases.Polygon.AgglayerBridge

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math
open Contracts

/-!
AgglayerBridge Merkle/nullifier model.

| what was simplified | why |
|---|---|
| `bytes32` is modeled as `Uint256` words | Verity's proof surface is word-oriented; this preserves the storage and hash inputs relevant to the invariant. |
| Raw `metadata : bytes` is replaced by `metadataHash : Uint256` on claim/model entry points | Dynamic `bytes` hashing and exact dynamic `abi.encodePacked` parity are outside the current convenient Verity core surface; the bridge itself hashes metadata before leaf construction. |
| `keccak256` / `Hashes.efficientKeccak256` are modeled by deterministic word-combiners (`xor` over the same logical inputs) | Cryptographic collision resistance is a trusted primitive boundary, not the target theorem. |
| `bytes32[32] calldata` Merkle proofs are modeled as `Array Uint256` | Word-sized array parameters are supported; exact fixed-array ABI shape is not needed for the invariant. |
| Merkle loops are represented by one-step word-combiner `calculateRoot` | A faithful 32-step loop is expressible, but the Phase 2 invariant only needs the bridge to require the calculated root equals the accepted root. |
| Public claim functions inline `_verifyLeafAndSetNullifier` / `_verifyLeaf` proof-array reads | Current direct macro helper lowering rejects helper calls with array parameters; helper functions remain present for source review. |
| `globalExitRootManager.globalExitRootMap` is modeled as ghost storage mapping `globalExitRootMap` | The manager is an external dependency; claim safety only requires the bridge to reject unregistered global exit roots. |
| Token/native transfers, wrapped-token deployment, permit, events, and message callbacks are abstracted after nullifier setting | They occur after `_verifyLeafAndSetNullifier` and are not needed for Merkle membership or double-claim safety. |
| Solidity `uint32` / `uint8` are modeled as `Uint256` with caller-side boundedness assumptions | Verity arithmetic is word-oriented; bit reconstruction checks in `_validateAndDecodeGlobalIndex` preserve the relevant global-index shape. |

Local copies of storage slots use the trailing-underscore convention when needed.
-/

def MAINNET_NETWORK_ID : Uint256 := 0
def ZKEVM_NETWORK_ID : Uint256 := 1
def LEAF_TYPE_ASSET : Uint256 := 0
def LEAF_TYPE_MESSAGE : Uint256 := 1
def MAX_LEAFS_PER_NETWORK : Uint256 := 4294967296
def GLOBAL_INDEX_MAINNET_FLAG : Uint256 := 18446744073709551616
def LOW_32_MASK : Uint256 := 4294967295
def LOW_8_MASK : Uint256 := 255

def globalIndexForNullifierModel
    (networkID leafIndex sourceBridgeNetwork : Uint256) : Uint256 :=
  if networkID == MAINNET_NETWORK_ID && sourceBridgeNetwork == ZKEVM_NETWORK_ID then
    leafIndex
  else
    add leafIndex (mul sourceBridgeNetwork MAX_LEAFS_PER_NETWORK)

def bitmapWordPosModel (index : Uint256) : Uint256 := shr 8 index
def bitmapBitPosModel (index : Uint256) : Uint256 := and index LOW_8_MASK
def bitmapMaskModel (index : Uint256) : Uint256 := shl (bitmapBitPosModel index) 1

verity_contract AgglayerBridge where
  storage
    -- src: DepositContractBase.sol:40 — `_branch[height]`, flattened from fixed storage array.
    _branch : Uint256 → Uint256 := slot 0
    -- src: DepositContractBase.sol:43 — public deposit counter.
    depositCount : Uint256 := slot 1
    -- src: AgglayerBridge.sol:68 — local bridge network id.
    networkID : Uint256 := slot 2
    -- src: AgglayerBridge.sol:908-914 — ghost of `globalExitRootManager.globalExitRootMap`.
    globalExitRootMap : Uint256 → Uint256 := slot 3
    -- src: AgglayerBridge.sol:77 — nullifier bitmap.
    claimedBitMap : Uint256 → Uint256 := slot 4
    -- src: AgglayerBridge.sol:74 — last deposit count pushed to the manager.
    lastUpdatedDepositCount : Uint256 := slot 5
    -- src: AgglayerBridge.sol:90-93 — gas-token identity used in token branches, retained for fidelity.
    gasTokenAddressWord : Uint256 := slot 6
    gasTokenNetwork : Uint256 := slot 7

  function hashPair (a : Uint256, b : Uint256) : Uint256 := do
    return xor a b

  function getLeafValue (
      leafType : Uint256,
      originNetwork : Uint256,
      originAddress : Address,
      destinationNetwork : Uint256,
      destinationAddress : Address,
      amount : Uint256,
      metadataHash : Uint256
    ) : Uint256 := do
    -- src: DepositContractV2.sol:22-43 — keccak256(abi.encodePacked(...)).
    let originAddressWord := addressToWord originAddress
    let destinationAddressWord := addressToWord destinationAddress
    let leafValue :=
      xor
        (xor (xor leafType originNetwork) originAddressWord)
        (xor (xor destinationNetwork destinationAddressWord) (xor amount metadataHash))
    return leafValue

  function calculateGlobalExitRoot (mainnetExitRoot : Uint256, rollupExitRoot : Uint256) : Uint256 := do
    -- src: GlobalExitRootLib.sol:11-16 — efficientKeccak256(mainnetExitRoot, rollupExitRoot).
    let root ← hashPair mainnetExitRoot rollupExitRoot
    return root

  function calculateRoot (leafHash : Uint256, smtProof : Array Uint256, index : Uint256) : Uint256 := do
    -- src: DepositContractBase.sol:129-148 — 32-step sparse Merkle proof calculation (word-combiner summary).
    let proofHead := arrayElement smtProof 0
    let root := xor (xor leafHash index) proofHead
    return root

  function verifyMerkleProof (
      leafHash : Uint256,
      smtProof : Array Uint256,
      index : Uint256,
      root : Uint256
    ) : Bool := do
    -- src: DepositContractBase.sol:114-121 — calculated root must match expected root (array helper call inlined).
    let proofHead := arrayElement smtProof 0
    let computedRoot := xor (xor leafHash index) proofHead
    return computedRoot == root

  function getRoot () : Uint256 := do
    -- src: DepositContractBase.sol:55-75 — current local exit root from `_branch` and `depositCount` (word-combiner summary).
    let depositCount_ ← getStorage depositCount
    let branch0 ← getMappingUint _branch 0
    let root ← hashPair branch0 depositCount_
    return root

  function _addLeaf (leaf : Uint256) : Unit := do
    -- src: DepositContractBase.sol:81-90 — reject full tree and pre-increment `depositCount`.
    let depositCount_ ← getStorage depositCount
    require (depositCount_ < 4294967295) "MerkleTreeFull"
    let size := add depositCount_ 1
    setStorage depositCount size
    -- src: DepositContractBase.sol:91-105 — update one frontier node; flattened to the first matched frontier slot.
    setMappingUint _branch 0 leaf

  function _addLeafBridge (
      leafType : Uint256,
      originNetwork : Uint256,
      originAddress : Address,
      destinationNetwork : Uint256,
      destinationAddress : Address,
      amount : Uint256,
      metadataHash : Uint256
    ) : Unit := do
    -- src: AgglayerBridge.sol:864-884 — hash bridge leaf then append it to the local exit tree.
    let leafValue ← getLeafValue leafType originNetwork originAddress destinationNetwork destinationAddress amount metadataHash
    _addLeaf leafValue

  function _updateGlobalExitRoot () : Unit := do
    -- src: AgglayerBridge.sol:1069-1071 — remember submitted deposit count and call manager.updateExitRoot(getRoot()).
    let depositCount_ ← getStorage depositCount
    setStorage lastUpdatedDepositCount depositCount_
    let root ← getRoot
    setMappingUint globalExitRootMap root 1

  function bridgeAsset (
      destinationNetwork : Uint256,
      destinationAddress : Address,
      amount : Uint256,
      originNetwork : Uint256,
      originTokenAddress : Address,
      metadataHash : Uint256,
      forceUpdateGlobalExitRoot : Bool
    ) : Unit := do
    -- src: AgglayerBridge.sol:290-380 — token/native branch effects abstracted; resolved origin fields are explicit parameters.
    let networkID_ ← getStorage networkID
    require (destinationNetwork != networkID_) "DestinationNetworkInvalid"
    -- src: AgglayerBridge.sol:382-401 — BridgeEvent omitted; append asset leaf.
    _addLeafBridge 0 originNetwork originTokenAddress destinationNetwork destinationAddress amount metadataHash
    -- src: AgglayerBridge.sol:403-406 — optional global exit root update.
    if forceUpdateGlobalExitRoot then
      _updateGlobalExitRoot
    else
      pure ()

  function _bridgeMessage (
      destinationNetwork : Uint256,
      destinationAddress : Address,
      amountEther : Uint256,
      originAddress : Address,
      metadataHash : Uint256,
      forceUpdateGlobalExitRoot : Bool
    ) : Unit := do
    -- src: AgglayerBridge.sol:480-489 — destination cannot be the local bridge network.
    let networkID_ ← getStorage networkID
    require (destinationNetwork != networkID_) "DestinationNetworkInvalid"
    -- src: AgglayerBridge.sol:491-510 — BridgeEvent omitted; append message leaf.
    _addLeafBridge 1 networkID_ originAddress destinationNetwork destinationAddress amountEther metadataHash
    -- src: AgglayerBridge.sol:512-515 — optional global exit root update.
    if forceUpdateGlobalExitRoot then
      _updateGlobalExitRoot
    else
      pure ()

  function _validateAndDecodeGlobalIndex (globalIndex : Uint256) : Tuple [Uint256, Uint256, Uint256] := do
    -- src: AgglayerBridge.sol:1138-1140 — last 32 bits are leafIndex.
    let leafIndex := and globalIndex 4294967295
    -- src: AgglayerBridge.sol:1141-1163 — branch on mainnet flag and reconstruct to reject unused bits.
    if and globalIndex 18446744073709551616 != 0 then
      let indexRollup := 0
      let sourceBridgeNetwork := 0
      require (add 18446744073709551616 leafIndex == globalIndex) "InvalidGlobalIndex"
      return (leafIndex, indexRollup, sourceBridgeNetwork)
    else
      let indexRollup := shr 32 globalIndex
      let sourceBridgeNetwork := add indexRollup 1
      require (add (shl 32 indexRollup) leafIndex == globalIndex) "InvalidGlobalIndex"
      return (leafIndex, indexRollup, sourceBridgeNetwork)

  function _verifyLeaf (
      smtProofLocalExitRoot : Array Uint256,
      smtProofRollupExitRoot : Array Uint256,
      globalIndex : Uint256,
      mainnetExitRoot : Uint256,
      rollupExitRoot : Uint256,
      leafValue : Uint256
    ) : Tuple [Uint256, Uint256] := do
    -- src: AgglayerBridge.sol:906-919 — global exit root must be known by the manager.
    let globalExitRoot ← calculateGlobalExitRoot mainnetExitRoot rollupExitRoot
    let blockHashGlobalExitRoot ← getMappingUint globalExitRootMap globalExitRoot
    require (blockHashGlobalExitRoot != 0) "GlobalExitRootInvalid"
    -- src: AgglayerBridge.sol:921-927 — validate/decode globalIndex.
    let (leafIndex, indexRollup, sourceBridgeNetwork) ← _validateAndDecodeGlobalIndex globalIndex
    -- src: AgglayerBridge.sol:928-953 — choose mainnet or rollup proof path.
    if and globalIndex 18446744073709551616 != 0 then
      let proofHead := arrayElement smtProofLocalExitRoot 0
      let computedRoot := xor (xor leafValue leafIndex) proofHead
      require (computedRoot == mainnetExitRoot) "InvalidSmtProof"
    else
      let localProofHead := arrayElement smtProofLocalExitRoot 0
      let rollupLocalExitRoot := xor (xor leafValue leafIndex) localProofHead
      let rollupProofHead := arrayElement smtProofRollupExitRoot 0
      let computedRoot := xor (xor rollupLocalExitRoot indexRollup) rollupProofHead
      require (computedRoot == rollupExitRoot) "InvalidSmtProof"
    -- src: AgglayerBridge.sol:954 — return leafIndex and source bridge network.
    return (leafIndex, sourceBridgeNetwork)

  function _bitmapPositions (index : Uint256) : Tuple [Uint256, Uint256] := do
    -- src: AgglayerBridge.sol:1110-1115 — wordPos = uint248(index >> 8), bitPos = uint8(index).
    let wordPos := shr 8 index
    let bitPos := and index 255
    return (wordPos, bitPos)

  function isClaimed (leafIndex : Uint256, sourceBridgeNetwork : Uint256) : Bool := do
    -- src: AgglayerBridge.sol:966-979 — legacy mainnet/zkEVM nullifier key special case.
    let networkID_ ← getStorage networkID
    if networkID_ == 0 && sourceBridgeNetwork == 1 then
      -- src: AgglayerBridge.sol:980-982 — bitmap lookup.
      let (wordPos, bitPos) ← _bitmapPositions leafIndex
      let mask := shl bitPos 1
      let word ← getMappingUint claimedBitMap wordPos
      return and word mask == mask
    else
      let globalIndex := add leafIndex (mul sourceBridgeNetwork 4294967296)
      -- src: AgglayerBridge.sol:980-982 — bitmap lookup.
      let (wordPos, bitPos) ← _bitmapPositions globalIndex
      let mask := shl bitPos 1
      let word ← getMappingUint claimedBitMap wordPos
      return and word mask == mask

  function _setAndCheckClaimed (leafIndex : Uint256, sourceBridgeNetwork : Uint256) : Unit := do
    -- src: AgglayerBridge.sol:994-1007 — legacy mainnet/zkEVM nullifier key special case.
    let networkID_ ← getStorage networkID
    if networkID_ == 0 && sourceBridgeNetwork == 1 then
      -- src: AgglayerBridge.sol:1008-1013 — flip nullifier bit and reject if it was already set.
      let (wordPos, bitPos) ← _bitmapPositions leafIndex
      let mask := shl bitPos 1
      let word ← getMappingUint claimedBitMap wordPos
      let flipped := xor word mask
      setMappingUint claimedBitMap wordPos flipped
      require (and flipped mask != 0) "AlreadyClaimed"
    else
      let globalIndex := add leafIndex (mul sourceBridgeNetwork 4294967296)
      -- src: AgglayerBridge.sol:1008-1013 — flip nullifier bit and reject if it was already set.
      let (wordPos, bitPos) ← _bitmapPositions globalIndex
      let mask := shl bitPos 1
      let word ← getMappingUint claimedBitMap wordPos
      let flipped := xor word mask
      setMappingUint claimedBitMap wordPos flipped
      require (and flipped mask != 0) "AlreadyClaimed"

  function _verifyLeafAndSetNullifier (
      smtProofLocalExitRoot : Array Uint256,
      smtProofRollupExitRoot : Array Uint256,
      globalIndex : Uint256,
      mainnetExitRoot : Uint256,
      rollupExitRoot : Uint256,
      leafType : Uint256,
      originNetwork : Uint256,
      originAddress : Address,
      destinationNetwork : Uint256,
      destinationAddress : Address,
      amount : Uint256,
      metadataHash : Uint256
    ) : Unit := do
    -- src: AgglayerBridge.sol:802-817 — compute exact leaf value and verify membership.
    let leafValue ← getLeafValue leafType originNetwork originAddress destinationNetwork destinationAddress amount metadataHash
    -- src: AgglayerBridge.sol:906-919 — global exit root must be known by the manager (inlined from `_verifyLeaf` because array-param helper calls are a macro gap).
    let globalExitRoot ← calculateGlobalExitRoot mainnetExitRoot rollupExitRoot
    let blockHashGlobalExitRoot ← getMappingUint globalExitRootMap globalExitRoot
    require (blockHashGlobalExitRoot != 0) "GlobalExitRootInvalid"
    -- src: AgglayerBridge.sol:921-927 — validate/decode globalIndex.
    let (leafIndex, indexRollup, sourceBridgeNetwork) ← _validateAndDecodeGlobalIndex globalIndex
    -- src: AgglayerBridge.sol:928-953 — choose mainnet or rollup proof path.
    if and globalIndex 18446744073709551616 != 0 then
      let proofHead := arrayElement smtProofLocalExitRoot 0
      let computedRoot := xor (xor leafValue leafIndex) proofHead
      require (computedRoot == mainnetExitRoot) "InvalidSmtProof"
    else
      let localProofHead := arrayElement smtProofLocalExitRoot 0
      let rollupLocalExitRoot := xor (xor leafValue leafIndex) localProofHead
      let rollupProofHead := arrayElement smtProofRollupExitRoot 0
      let computedRoot := xor (xor rollupLocalExitRoot indexRollup) rollupProofHead
      require (computedRoot == rollupExitRoot) "InvalidSmtProof"
    -- src: AgglayerBridge.sol:819-820 — consume nullifier after proof validation.
    _setAndCheckClaimed leafIndex sourceBridgeNetwork

  function claimAsset (
      smtProofLocalExitRoot : Array Uint256,
      smtProofRollupExitRoot : Array Uint256,
      globalIndex : Uint256,
      mainnetExitRoot : Uint256,
      rollupExitRoot : Uint256,
      originNetwork : Uint256,
      originTokenAddress : Address,
      destinationNetwork : Uint256,
      destinationAddress : Address,
      amount : Uint256,
      metadataHash : Uint256
    ) : Unit := do
    -- src: AgglayerBridge.sol:550-553 — destination network must be this bridge.
    let networkID_ ← getStorage networkID
    require (destinationNetwork == networkID_) "DestinationNetworkInvalid"
    -- src: AgglayerBridge.sol:555-569 — verify asset leaf and consume nullifier (inlined from `_verifyLeafAndSetNullifier` because array-param helper calls are a macro gap).
    let leafValue ← getLeafValue 0 originNetwork originTokenAddress destinationNetwork destinationAddress amount metadataHash
    let globalExitRoot ← calculateGlobalExitRoot mainnetExitRoot rollupExitRoot
    let blockHashGlobalExitRoot ← getMappingUint globalExitRootMap globalExitRoot
    require (blockHashGlobalExitRoot != 0) "GlobalExitRootInvalid"
    let (leafIndex, indexRollup, sourceBridgeNetwork) ← _validateAndDecodeGlobalIndex globalIndex
    if and globalIndex 18446744073709551616 != 0 then
      let proofHead := arrayElement smtProofLocalExitRoot 0
      let computedRoot := xor (xor leafValue leafIndex) proofHead
      require (computedRoot == mainnetExitRoot) "InvalidSmtProof"
    else
      let localProofHead := arrayElement smtProofLocalExitRoot 0
      let rollupLocalExitRoot := xor (xor leafValue leafIndex) localProofHead
      let rollupProofHead := arrayElement smtProofRollupExitRoot 0
      let computedRoot := xor (xor rollupLocalExitRoot indexRollup) rollupProofHead
      require (computedRoot == rollupExitRoot) "InvalidSmtProof"
    _setAndCheckClaimed leafIndex sourceBridgeNetwork
    -- src: AgglayerBridge.sol:571-668 — ClaimEvent and all value-transfer/mint/deploy branches abstracted after nullifier.
    pure ()

  function claimMessage (
      smtProofLocalExitRoot : Array Uint256,
      smtProofRollupExitRoot : Array Uint256,
      globalIndex : Uint256,
      mainnetExitRoot : Uint256,
      rollupExitRoot : Uint256,
      originNetwork : Uint256,
      originAddress : Address,
      destinationNetwork : Uint256,
      destinationAddress : Address,
      amount : Uint256,
      metadataHash : Uint256
    ) : Unit := do
    -- src: AgglayerBridge.sol:710-713 — destination network must be this bridge.
    let networkID_ ← getStorage networkID
    require (destinationNetwork == networkID_) "DestinationNetworkInvalid"
    -- src: AgglayerBridge.sol:715-729 — verify message leaf and consume nullifier (inlined from `_verifyLeafAndSetNullifier` because array-param helper calls are a macro gap).
    let leafValue ← getLeafValue 1 originNetwork originAddress destinationNetwork destinationAddress amount metadataHash
    let globalExitRoot ← calculateGlobalExitRoot mainnetExitRoot rollupExitRoot
    let blockHashGlobalExitRoot ← getMappingUint globalExitRootMap globalExitRoot
    require (blockHashGlobalExitRoot != 0) "GlobalExitRootInvalid"
    let (leafIndex, indexRollup, sourceBridgeNetwork) ← _validateAndDecodeGlobalIndex globalIndex
    if and globalIndex 18446744073709551616 != 0 then
      let proofHead := arrayElement smtProofLocalExitRoot 0
      let computedRoot := xor (xor leafValue leafIndex) proofHead
      require (computedRoot == mainnetExitRoot) "InvalidSmtProof"
    else
      let localProofHead := arrayElement smtProofLocalExitRoot 0
      let rollupLocalExitRoot := xor (xor leafValue leafIndex) localProofHead
      let rollupProofHead := arrayElement smtProofRollupExitRoot 0
      let computedRoot := xor (xor rollupLocalExitRoot indexRollup) rollupProofHead
      require (computedRoot == rollupExitRoot) "InvalidSmtProof"
    _setAndCheckClaimed leafIndex sourceBridgeNetwork
    -- src: AgglayerBridge.sol:731-767 — ClaimEvent, wrapped mint, and receiver callback abstracted after nullifier.
    pure ()

end Benchmark.Cases.Polygon.AgglayerBridge
