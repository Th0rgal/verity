// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyNamespacedStorageSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyNamespacedStorageSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYulWithArgs("NamespacedStorageSmoke", abi.encode(alice));
        require(target != address(0), "Deploy failed");
    }

    // Property 1: deposit has no unexpected revert
    function testAuto_Deposit_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("deposit(uint256)", uint256(1)));
        require(ok, "deposit reverted unexpectedly");
    }
    // Property 2: getOwner reads storage slot 1 and decodes the result
    function testAuto_GetOwner_ReadsConfiguredStorage() public {
        address expected = alice;
        vm.store(target, bytes32(uint256(1)), bytes32(uint256(uint160(expected))));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("getOwner()"));
        require(ok, "getOwner reverted unexpectedly");
        assertEq(ret.length, 32, "getOwner ABI return length mismatch (expected 32 bytes)");
        address actual = abi.decode(ret, (address));
        assertEq(actual, expected, "getOwner should return storage slot 1");
    }
}
