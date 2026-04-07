// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyStorageBoolArraySmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyStorageBoolArraySmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("StorageBoolArraySmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: firstFlag reads the configured storage-array element
    function testAuto_FirstFlag_ReadsConfiguredStorageArrayElement() public {
        bool expected = true;
        vm.store(target, bytes32(uint256(0)), bytes32(uint256(1)));
        vm.store(target, bytes32(uint256(keccak256(abi.encode(uint256(0)))) + 0), bytes32(uint256(expected ? 1 : 0)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("firstFlag()"));
        require(ok, "firstFlag reverted unexpectedly");
        assertEq(ret.length, 32, "firstFlag ABI return length mismatch (expected 32 bytes)");
        bool actual = abi.decode(ret, (bool));
        assertEq(actual, expected, "firstFlag should return the configured array element");
    }
    // Property 2: pushFlag has no unexpected revert
    function testAuto_PushFlag_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("pushFlag(bool)", true));
        require(ok, "pushFlag reverted unexpectedly");
    }
    // Property 3: setFirstFlag has no unexpected revert
    function testAuto_SetFirstFlag_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("setFirstFlag(bool)", true));
        require(ok, "setFirstFlag reverted unexpectedly");
    }
}
