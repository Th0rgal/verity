// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyPackedStorageWriteSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyPackedStorageWriteSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("PackedStorageWriteSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: writeSlot0 has no unexpected revert
    function testAuto_WriteSlot0_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("writeSlot0(bool,uint256)", true, uint256(1)));
        require(ok, "writeSlot0 reverted unexpectedly");
    }
    // Property 2: writeSlot1 has no unexpected revert
    function testAuto_WriteSlot1_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("writeSlot1(uint256,uint256)", uint256(1), uint256(1)));
        require(ok, "writeSlot1 reverted unexpectedly");
    }
}
