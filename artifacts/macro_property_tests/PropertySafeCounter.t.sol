// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertySafeCounterTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/SafeCounter/SafeCounter.lean
 */
contract PropertySafeCounterTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("SafeCounter");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: increment has no unexpected revert
    function testAuto_Increment_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("increment()"));
        require(ok, "increment reverted unexpectedly");
    }
    // Property 2: decrement has no unexpected revert
    function testAuto_Decrement_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("decrement()"));
        require(ok, "decrement reverted unexpectedly");
    }
    // Property 3: getCount reads storage slot 0 and decodes the result
    function testAuto_GetCount_ReadsConfiguredStorage() public {
        uint256 expected = uint256(1);
        vm.store(target, bytes32(uint256(0)), bytes32(uint256(expected)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("getCount()"));
        require(ok, "getCount reverted unexpectedly");
        assertEq(ret.length, 32, "getCount ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, expected, "getCount should return storage slot 0");
    }
}
