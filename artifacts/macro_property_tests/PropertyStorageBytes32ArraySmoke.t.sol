// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyStorageBytes32ArraySmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyStorageBytes32ArraySmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("StorageBytes32ArraySmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: firstDigest reads the configured storage-array element
    function testAuto_FirstDigest_ReadsConfiguredStorageArrayElement() public {
        bytes32 expected = bytes32(uint256(0xBEEF));
        vm.store(target, bytes32(uint256(0)), bytes32(uint256(1)));
        vm.store(target, bytes32(uint256(keccak256(abi.encode(uint256(0)))) + 0), expected);
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("firstDigest()"));
        require(ok, "firstDigest reverted unexpectedly");
        assertEq(ret.length, 32, "firstDigest ABI return length mismatch (expected 32 bytes)");
        bytes32 actual = abi.decode(ret, (bytes32));
        assertEq(actual, expected, "firstDigest should return the configured array element");
    }
    // Property 2: pushDigest has no unexpected revert
    function testAuto_PushDigest_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("pushDigest(bytes32)", bytes32(uint256(0xBEEF))));
        require(ok, "pushDigest reverted unexpectedly");
    }
}
