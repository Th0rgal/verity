// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";

abstract contract DiffTestConfig is Test {
    function _diffRandomSmallCount() internal view returns (uint256) {
        return vm.envOr("DIFFTEST_RANDOM_SMALL", uint256(100));
    }

    function _diffRandomLargeCount() internal view returns (uint256) {
        return vm.envOr("DIFFTEST_RANDOM_LARGE", uint256(10000));
    }

    function _diffRandomSeed() internal view returns (uint256) {
        return vm.envOr("DIFFTEST_RANDOM_SEED", uint256(42));
    }
}
