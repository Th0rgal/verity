// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";

abstract contract DiffTestConfig is Test {
    /// @notice Report the random seed being used for this test run
    /// @dev Call this in setUp() to log the seed for reproducibility
    function _reportRandomSeed() internal view {
        uint256 seed = _diffRandomBaseSeed();
        uint256 shardIndex = _diffShardIndex();
        uint256 shardCount = _diffShardCount();

        if (shardCount > 1) {
            console.log("DIFFTEST_RANDOM_SEED:", seed);
            console.log("Shard:", shardIndex, "/", shardCount);
        } else {
            console.log("DIFFTEST_RANDOM_SEED:", seed);
        }
    }

    function _diffShardIndex() internal view returns (uint256) {
        return vm.envOr("DIFFTEST_SHARD_INDEX", uint256(0));
    }

    function _diffShardCount() internal view returns (uint256) {
        return vm.envOr("DIFFTEST_SHARD_COUNT", uint256(1));
    }

    function _diffShardRange(uint256 totalCount) internal view returns (uint256 start, uint256 count) {
        uint256 shardCount = _diffShardCount();
        require(shardCount > 0, "DIFFTEST_SHARD_COUNT must be > 0");
        uint256 shardIndex = _diffShardIndex();
        require(shardIndex < shardCount, "DIFFTEST_SHARD_INDEX out of range");

        start = (totalCount * shardIndex) / shardCount;
        uint256 end = (totalCount * (shardIndex + 1)) / shardCount;
        count = end - start;
    }

    function _diffRandomOverride() internal view returns (uint256) {
        return vm.envOr("DIFFTEST_RANDOM_COUNT", uint256(0));
    }

    function _diffRandomSmallRange() internal view returns (uint256 start, uint256 count) {
        uint256 overrideCount = _diffRandomOverride();
        uint256 totalCount =
            overrideCount != 0 ? overrideCount : vm.envOr("DIFFTEST_RANDOM_SMALL", uint256(100));
        return _diffShardRange(totalCount);
    }

    function _diffRandomLargeRange() internal view returns (uint256 start, uint256 count) {
        uint256 overrideCount = _diffRandomOverride();
        uint256 totalCount =
            overrideCount != 0 ? overrideCount : vm.envOr("DIFFTEST_RANDOM_LARGE", uint256(10000));
        return _diffShardRange(totalCount);
    }

    function _diffRandomBaseSeed() internal view returns (uint256) {
        return vm.envOr("DIFFTEST_RANDOM_SEED", uint256(42));
    }

    function _diffRandomSeed(string memory label) internal view returns (uint256) {
        return uint256(keccak256(abi.encodePacked(_diffRandomBaseSeed(), _diffShardIndex(), label))) % (2**31);
    }

    function _diffVerbose() internal view returns (bool) {
        return vm.envOr("DIFFTEST_VERBOSE", false);
    }

    function _lcg(uint256 prng) internal pure returns (uint256) {
        return (1103515245 * prng + 12345) % (2**31);
    }

    function _edgeUintValues() internal pure returns (uint256[] memory) {
        uint256[] memory values = new uint256[](5);
        values[0] = 0;
        values[1] = 1;
        values[2] = 2;
        values[3] = type(uint256).max - 1;
        values[4] = type(uint256).max;
        return values;
    }

    function _assertRandomSuccess(bool success, uint256 iteration) internal {
        if (!success) {
            emit log_named_uint("Random test failed at", iteration);
            fail();
        }
    }
}
