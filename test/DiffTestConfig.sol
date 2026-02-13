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

    function _diffRandomOverride() internal view returns (uint256) {
        return vm.envOr("DIFFTEST_RANDOM_COUNT", uint256(0));
    }

    function _diffRandomSmallCount() internal view returns (uint256) {
        uint256 overrideCount = _diffRandomOverride();
        if (overrideCount != 0) {
            return _diffShardAdjustedCount(overrideCount);
        }
        return _diffShardAdjustedCount(vm.envOr("DIFFTEST_RANDOM_SMALL", uint256(100)));
    }

    function _diffRandomLargeCount() internal view returns (uint256) {
        uint256 overrideCount = _diffRandomOverride();
        if (overrideCount != 0) {
            return _diffShardAdjustedCount(overrideCount);
        }
        return _diffShardAdjustedCount(vm.envOr("DIFFTEST_RANDOM_LARGE", uint256(10000)));
    }

    function _diffRandomSeed() internal view returns (uint256) {
        uint256 seed = vm.envOr("DIFFTEST_RANDOM_SEED", uint256(42));
        uint256 shardIndex = _diffShardIndex();
        uint256 shardCount = _diffShardCount();
        require(shardIndex < shardCount, "DIFFTEST_SHARD_INDEX out of range");

        unchecked {
            return seed + (shardIndex * 0x9e3779b97f4a7c15);
        }
    }

    function _diffVerbose() internal view returns (bool) {
        return vm.envOr("DIFFTEST_VERBOSE", false);
    }

    function _assertRandomSuccess(bool success, uint256 iteration) internal {
        if (!success) {
            emit log_named_uint("Random test failed at", iteration);
            fail();
        }
    }
}
