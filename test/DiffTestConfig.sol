// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";

abstract contract DiffTestConfig is Test {
    function _diffShardIndex() internal view returns (uint256) {
        return vm.envOr("DIFFTEST_SHARD_INDEX", uint256(0));
    }

    function _diffShardCount() internal view returns (uint256) {
        return vm.envOr("DIFFTEST_SHARD_COUNT", uint256(1));
    }

    function _diffShardAdjustedCount(uint256 totalCount) internal view returns (uint256) {
        uint256 shardCount = _diffShardCount();
        require(shardCount > 0, "DIFFTEST_SHARD_COUNT must be > 0");
        uint256 shardIndex = _diffShardIndex();
        require(shardIndex < shardCount, "DIFFTEST_SHARD_INDEX out of range");

        uint256 start = (totalCount * shardIndex) / shardCount;
        uint256 end = (totalCount * (shardIndex + 1)) / shardCount;
        return end - start;
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

    function _diffRandomSeed() internal view returns (uint256) {
        uint256 seed = _diffRandomBaseSeed();
        uint256 shardIndex = _diffShardIndex();
        uint256 shardCount = _diffShardCount();
        require(shardIndex < shardCount, "DIFFTEST_SHARD_INDEX out of range");

        unchecked {
            return seed + (shardIndex * 0x9e3779b97f4a7c15);
        }
    }

    function _diffRandomSmallConfig() internal view returns (uint256 start, uint256 count, uint256 seed) {
        (start, count) = _diffRandomSmallRange();
        seed = _diffRandomSeed();
    }

    function _diffRandomLargeConfig() internal view returns (uint256 start, uint256 count, uint256 seed) {
        (start, count) = _diffRandomLargeRange();
        seed = _diffRandomSeed();
    }

    function _diffVerbose() internal view returns (bool) {
        return vm.envOr("DIFFTEST_VERBOSE", false);
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
