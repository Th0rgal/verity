// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyStorageWordsAddressSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyStorageWordsAddressSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("StorageWordsAddressSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: TODO decode and assert `extSloadsLike` result
    function testTODO_ExtSloadsLike_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("extSloadsLike(address[])", _singletonAddressArray(alice)));
        require(ok, "extSloadsLike reverted unexpectedly");
        require(ret.length >= 64, "extSloadsLike ABI dynamic return payload unexpectedly short");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }

    function _singletonAddressArray(address x) internal pure returns (address[] memory arr) {
        arr = new address[](1);
        arr[0] = x;
    }
}
