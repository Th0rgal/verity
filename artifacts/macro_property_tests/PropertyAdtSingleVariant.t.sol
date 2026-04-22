// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyAdtSingleVariantTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyAdtSingleVariantTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("AdtSingleVariant");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: store has no unexpected revert
    function testAuto_Store_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("store()"));
        require(ok, "store reverted unexpectedly");
    }
}
