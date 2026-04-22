// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyRolesSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyRolesSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYulWithArgs("RolesSmoke", abi.encode(alice));
        require(target != address(0), "Deploy failed");
    }

    // Property 1: getCounter reads storage slot 1 and decodes the result
    function testAuto_GetCounter_ReadsConfiguredStorage() public {
        uint256 expected = uint256(1);
        vm.store(target, bytes32(uint256(1)), bytes32(uint256(expected)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("getCounter()"));
        require(ok, "getCounter reverted unexpectedly");
        assertEq(ret.length, 32, "getCounter ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, expected, "getCounter should return storage slot 1");
    }
}
