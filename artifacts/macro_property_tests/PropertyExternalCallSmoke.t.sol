// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyExternalCallSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyExternalCallSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("ExternalCallSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: storeEcho has no unexpected revert
    function testAuto_StoreEcho_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("storeEcho(uint256)", uint256(1)));
        require(ok, "storeEcho reverted unexpectedly");
    }
    // Property 2: getEchoedValue reads storage slot 0 and decodes the result
    function testAuto_GetEchoedValue_ReadsConfiguredStorage() public {
        uint256 expected = uint256(1);
        vm.store(target, bytes32(uint256(0)), bytes32(uint256(expected)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("getEchoedValue()"));
        require(ok, "getEchoedValue reverted unexpectedly");
        assertEq(ret.length, 32, "getEchoedValue ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, expected, "getEchoedValue should return storage slot 0");
    }
}
