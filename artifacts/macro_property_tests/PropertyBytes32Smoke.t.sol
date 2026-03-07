// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyBytes32SmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyBytes32SmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("Bytes32Smoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: setDigest has no unexpected revert
    function testAuto_SetDigest_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("setDigest(bytes32)", bytes32(uint256(0xBEEF))));
        require(ok, "setDigest reverted unexpectedly");
    }
    // Property 2: getDigest reads storage slot 0 and decodes the result
    function testAuto_GetDigest_ReadsConfiguredStorage() public {
        bytes32 expected = bytes32(uint256(0xBEEF));
        vm.store(target, bytes32(uint256(0)), expected);
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("getDigest()"));
        require(ok, "getDigest reverted unexpectedly");
        assertEq(ret.length, 32, "getDigest ABI return length mismatch (expected 32 bytes)");
        bytes32 actual = abi.decode(ret, (bytes32));
        assertEq(actual, expected, "getDigest should return storage slot 0");
    }
}
