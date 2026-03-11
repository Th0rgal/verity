// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyStatelessSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyStatelessSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("StatelessSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: echoWord returns the direct parameter value
    function testAuto_EchoWord_ReturnsDirectParam() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("echoWord(uint256)", uint256(1)));
        require(ok, "echoWord reverted unexpectedly");
        assertEq(ret.length, 32, "echoWord ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, uint256(1), "echoWord should preserve the expected value");
    }
    // Property 2: whoAmI returns the active caller
    function testAuto_WhoAmI_ReturnsMsgSender() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("whoAmI()"));
        require(ok, "whoAmI reverted unexpectedly");
        assertEq(ret.length, 32, "whoAmI ABI return length mismatch (expected 32 bytes)");
        address actual = abi.decode(ret, (address));
        assertEq(actual, alice, "whoAmI should preserve the expected value");
    }
}
