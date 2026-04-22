// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyNoExternalCallsSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyNoExternalCallsSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("NoExternalCallsSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: setOwner has no unexpected revert
    function testAuto_SetOwner_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("setOwner(address)", alice));
        require(ok, "setOwner reverted unexpectedly");
    }
}
