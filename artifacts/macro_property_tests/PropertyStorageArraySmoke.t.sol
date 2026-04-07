// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyStorageArraySmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyStorageArraySmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("StorageArraySmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: size reads the configured storage-array length
    function testAuto_Size_ReadsConfiguredStorageArrayLength() public {
        uint256 expected = uint256(1);
        vm.store(target, bytes32(uint256(0)), bytes32(expected));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("size()"));
        require(ok, "size reverted unexpectedly");
        assertEq(ret.length, 32, "size ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, expected, "size should return the configured array length");
    }
    // Property 2: push has no unexpected revert
    function testAuto_Push_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("push(uint256)", uint256(1)));
        require(ok, "push reverted unexpectedly");
    }
}
