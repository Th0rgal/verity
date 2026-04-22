// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyUnsafeGatingAcceptedTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyUnsafeGatingAcceptedTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("UnsafeGatingAccepted");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: writeMem has no unexpected revert
    function testAuto_WriteMem_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("writeMem()"));
        require(ok, "writeMem reverted unexpectedly");
    }
}
