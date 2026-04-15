// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyNewtypeStorageSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyNewtypeStorageSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYulWithArgs("NewtypeStorageSmoke", abi.encode(alice));
        require(target != address(0), "Deploy failed");
    }

    // Property 1: setTokenId has no unexpected revert
    function testAuto_SetTokenId_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("setTokenId(uint256)", uint256(1)));
        require(ok, "setTokenId reverted unexpectedly");
    }
    // Property 2: getTokenId reads storage slot 0 and decodes the result
    function testAuto_GetTokenId_ReadsConfiguredStorage() public {
        uint256 expected = uint256(1);
        vm.store(target, bytes32(uint256(0)), bytes32(uint256(expected)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("getTokenId()"));
        require(ok, "getTokenId reverted unexpectedly");
        assertEq(ret.length, 32, "getTokenId ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, expected, "getTokenId should return storage slot 0");
    }
    // Property 3: setAdmin has no unexpected revert
    function testAuto_SetAdmin_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("setAdmin(address)", alice));
        require(ok, "setAdmin reverted unexpectedly");
    }
    // Property 4: getAdmin reads storage slot 1 and decodes the result
    function testAuto_GetAdmin_ReadsConfiguredStorage() public {
        address expected = alice;
        vm.store(target, bytes32(uint256(1)), bytes32(uint256(uint160(expected))));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("getAdmin()"));
        require(ok, "getAdmin reverted unexpectedly");
        assertEq(ret.length, 32, "getAdmin ABI return length mismatch (expected 32 bytes)");
        address actual = abi.decode(ret, (address));
        assertEq(actual, expected, "getAdmin should return storage slot 1");
    }
}
