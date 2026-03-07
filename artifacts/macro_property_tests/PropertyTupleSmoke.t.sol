// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyTupleSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyTupleSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("TupleSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: setFromPair has no unexpected revert
    function testAuto_SetFromPair_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("setFromPair((uint256,uint256))", abi.encode(uint256(1), uint256(1))));
        require(ok, "setFromPair reverted unexpectedly");
    }
    // Property 2: getPair decodes and matches the returned tuple elements
    function testAuto_GetPair_DecodesTupleResult() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("getPair(uint256)", uint256(1)));
        require(ok, "getPair reverted unexpectedly");
        require(ret.length >= 64, "getPair ABI tuple return payload unexpectedly short");
        (uint256 actual0, uint256 actual1) = abi.decode(ret, (uint256, uint256));
        assertEq(actual0, uint256(1), "getPair tuple element 0 mismatch");
        assertEq(actual1, uint256(1), "getPair tuple element 1 mismatch");
    }
    // Property 3: processConfig has no unexpected revert
    function testAuto_ProcessConfig_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("processConfig((address,address,uint256))", abi.encode(alice, alice, uint256(1))));
        require(ok, "processConfig reverted unexpectedly");
    }
}
