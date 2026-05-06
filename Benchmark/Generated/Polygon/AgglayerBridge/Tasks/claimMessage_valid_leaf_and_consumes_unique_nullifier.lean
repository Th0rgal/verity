import Benchmark.Cases.Polygon.AgglayerBridge.Contract
import Benchmark.Cases.Polygon.AgglayerBridge.Specs

namespace Benchmark.Generated.Polygon.AgglayerBridge.Tasks

open Verity
open Verity.EVM.Uint256
open Benchmark.Cases.Polygon.AgglayerBridge

theorem claimMessage_valid_leaf_and_consumes_unique_nullifier
    (s : ContractState)
    (smtProofLocalExitRoot smtProofRollupExitRoot : Array Uint256)
    (globalIndex mainnetExitRoot rollupExitRoot originNetwork : Uint256)
    (originAddress : Address)
    (destinationNetwork : Uint256)
    (destinationAddress : Address)
    (amount metadataHash : Uint256) :
    match
      (AgglayerBridge.claimMessage
        smtProofLocalExitRoot smtProofRollupExitRoot globalIndex mainnetExitRoot rollupExitRoot
        originNetwork originAddress destinationNetwork destinationAddress amount metadataHash).run s
    with
    | ContractResult.success _ s' =>
        claimMessage_valid_leaf_and_consumes_unique_nullifier_spec
          s s' smtProofLocalExitRoot smtProofRollupExitRoot globalIndex mainnetExitRoot rollupExitRoot
          originNetwork originAddress destinationNetwork destinationAddress amount metadataHash
    | ContractResult.revert _ _ => True := by
  exact ?_

end Benchmark.Generated.Polygon.AgglayerBridge.Tasks
