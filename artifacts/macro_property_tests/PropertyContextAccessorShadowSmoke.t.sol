// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyContextAccessorShadowSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyContextAccessorShadowSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("ContextAccessorShadowSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: echoSenderName returns the direct parameter value
    function testAuto_EchoSenderName_ReturnsDirectParam() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("echoSenderName(address)", alice));
        require(ok, "echoSenderName reverted unexpectedly");
        assertEq(ret.length, 32, "echoSenderName ABI return length mismatch (expected 32 bytes)");
        address actual = abi.decode(ret, (address));
        assertEq(actual, alice, "echoSenderName should preserve the expected value");
    }
}
