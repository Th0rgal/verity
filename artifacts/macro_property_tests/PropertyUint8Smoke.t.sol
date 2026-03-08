// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyUint8SmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyUint8SmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("Uint8Smoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: acceptSig has no unexpected revert
    function testAuto_AcceptSig_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("acceptSig((uint8,bytes32,bytes32))", abi.decode(abi.encode(uint8(27), bytes32(uint256(0xBEEF)), bytes32(uint256(0xBEEF))), (uint8, bytes32, bytes32))));
        require(ok, "acceptSig reverted unexpectedly");
    }
    // Property 2: sigV returns the declared constant result
    function testAuto_SigV_ReturnsDeclaredConstant() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("sigV()"));
        require(ok, "sigV reverted unexpectedly");
        assertEq(ret.length, 32, "sigV ABI return length mismatch (expected 32 bytes)");
        uint8 actual = abi.decode(ret, (uint8));
        assertEq(actual, 27, "sigV should return the declared constant");
    }
}
