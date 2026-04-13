// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyExternalCallMultiReturnTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyExternalCallMultiReturnTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("ExternalCallMultiReturn");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: noop has no unexpected revert
    function testAuto_Noop_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("noop()"));
        require(ok, "noop reverted unexpectedly");
    }
}
