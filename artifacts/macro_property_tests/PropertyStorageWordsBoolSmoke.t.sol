// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyStorageWordsBoolSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyStorageWordsBoolSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("StorageWordsBoolSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: extSloadsLike returns the canonical storage words for the configured input slots
    function testAuto_ExtSloadsLike_ReturnsCanonicalStorageWords() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("extSloadsLike(bool[])", _singletonBoolArray(true)));
        require(ok, "extSloadsLike reverted unexpectedly");
        require(ret.length >= 64, "extSloadsLike ABI dynamic return payload unexpectedly short");
        uint256[] memory actual = abi.decode(ret, (uint256[]));
        assertEq(actual.length, 1, "extSloadsLike should return one word for the configured singleton input");
        assertEq(actual[0], (true ? 1 : 0), "extSloadsLike should return the canonical word for the configured input");
    }

    function _singletonBoolArray(bool x) internal pure returns (bool[] memory arr) {
        arr = new bool[](1);
        arr[0] = x;
    }
}
