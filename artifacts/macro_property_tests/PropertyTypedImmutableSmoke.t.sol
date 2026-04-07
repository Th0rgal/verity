// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyTypedImmutableSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyTypedImmutableSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("TypedImmutableSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: isPaused returns the declared constant or immutable value
    function testAuto_IsPaused_ReturnsDeclaredBinding() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("isPaused()"));
        require(ok, "isPaused reverted unexpectedly");
        assertEq(ret.length, 32, "isPaused ABI return length mismatch (expected 32 bytes)");
        bool actual = abi.decode(ret, (bool));
        assertEq(actual, true, "isPaused should preserve the expected value");
    }
    // Property 2: feeScale returns the declared constant or immutable value
    function testAuto_FeeScale_ReturnsDeclaredBinding() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("feeScale()"));
        require(ok, "feeScale reverted unexpectedly");
        assertEq(ret.length, 32, "feeScale ABI return length mismatch (expected 32 bytes)");
        uint8 actual = abi.decode(ret, (uint8));
        assertEq(actual, 7, "feeScale should preserve the expected value");
    }
    // Property 3: domainSeparator returns the declared constant or immutable value
    function testAuto_DomainSeparator_ReturnsDeclaredBinding() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("domainSeparator()"));
        require(ok, "domainSeparator reverted unexpectedly");
        assertEq(ret.length, 32, "domainSeparator ABI return length mismatch (expected 32 bytes)");
        bytes32 actual = abi.decode(ret, (bytes32));
        assertEq(actual, bytes32(uint256(42)), "domainSeparator should preserve the expected value");
    }
}
