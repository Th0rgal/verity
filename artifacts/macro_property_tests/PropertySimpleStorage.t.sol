// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertySimpleStorageTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/SimpleStorage/SimpleStorage.lean
 */
contract PropertySimpleStorageTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("SimpleStorage");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: store has no unexpected revert
    function testAuto_Store_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("store(uint256)", uint256(1)));
        require(ok, "store reverted unexpectedly");
    }
    // Property 2: retrieve reads storage slot 0 and decodes the result
    function testAuto_Retrieve_ReadsConfiguredStorage() public {
        uint256 expected = uint256(1);
        vm.store(target, bytes32(uint256(0)), bytes32(uint256(expected)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("retrieve()"));
        require(ok, "retrieve reverted unexpectedly");
        assertEq(ret.length, 32, "retrieve ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, expected, "retrieve should return storage slot 0");
    }
}
