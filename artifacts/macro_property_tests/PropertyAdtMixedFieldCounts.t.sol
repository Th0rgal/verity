// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyAdtMixedFieldCountsTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyAdtMixedFieldCountsTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("AdtMixedFieldCounts");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: clear has no unexpected revert
    function testAuto_Clear_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("clear()"));
        require(ok, "clear reverted unexpectedly");
    }
    // Property 2: set has no unexpected revert
    function testAuto_Set_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("set(uint256)", uint256(1)));
        require(ok, "set reverted unexpectedly");
    }
}
