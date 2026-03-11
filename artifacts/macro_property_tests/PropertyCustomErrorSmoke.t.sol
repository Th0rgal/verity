// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyCustomErrorSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyCustomErrorSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("CustomErrorSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: echo returns the direct parameter value
    function testAuto_Echo_ReturnsDirectParam() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("echo(uint256)", uint256(1)));
        require(ok, "echo reverted unexpectedly");
        assertEq(ret.length, 32, "echo ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, uint256(1), "echo should preserve the expected value");
    }
}
