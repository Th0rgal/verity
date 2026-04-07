// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyStorageAddressArraySmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyStorageAddressArraySmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("StorageAddressArraySmoke");
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
    // Property 2: firstOwner reads the configured storage-array element
    function testAuto_FirstOwner_ReadsConfiguredStorageArrayElement() public {
        address expected = alice;
        vm.store(target, bytes32(uint256(0)), bytes32(uint256(1)));
        vm.store(target, bytes32(uint256(keccak256(abi.encode(uint256(0)))) + 0), bytes32(uint256(uint160(expected))));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("firstOwner()"));
        require(ok, "firstOwner reverted unexpectedly");
        assertEq(ret.length, 32, "firstOwner ABI return length mismatch (expected 32 bytes)");
        address actual = abi.decode(ret, (address));
        assertEq(actual, expected, "firstOwner should return the configured array element");
    }
    // Property 3: pushOwner has no unexpected revert
    function testAuto_PushOwner_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("pushOwner(address)", alice));
        require(ok, "pushOwner reverted unexpectedly");
    }
    // Property 4: replaceFirstOwner has no unexpected revert
    function testAuto_ReplaceFirstOwner_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("replaceFirstOwner(address)", alice));
        require(ok, "replaceFirstOwner reverted unexpectedly");
    }
}
