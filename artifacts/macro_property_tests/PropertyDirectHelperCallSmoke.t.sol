// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyDirectHelperCallSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyDirectHelperCallSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("DirectHelperCallSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: addToTotal has no unexpected revert
    function testAuto_AddToTotal_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("addToTotal(uint256)", uint256(1)));
        require(ok, "addToTotal reverted unexpectedly");
    }
    // Property 2: readTotalPlus decodes and matches the inferred straight-line result
    function testAuto_ReadTotalPlus_ReturnsInferredStraightLineResult() public {
        uint256 expected = uint256(1);
        vm.store(target, bytes32(uint256(0)), bytes32(uint256(expected)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("readTotalPlus(uint256)", uint256(1)));
        require(ok, "readTotalPlus reverted unexpectedly");
        assertEq(ret.length, 32, "readTotalPlus ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, (expected + uint256(1)), "readTotalPlus should preserve the inferred result");
    }
    // Property 3: pairWithTotal decodes and matches the inferred tuple result
    function testAuto_PairWithTotal_ReturnsInferredTupleResult() public {
        uint256 expected = uint256(1);
        vm.store(target, bytes32(uint256(0)), bytes32(uint256(expected)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("pairWithTotal(uint256)", uint256(1)));
        require(ok, "pairWithTotal reverted unexpectedly");
        require(ret.length >= 64, "pairWithTotal ABI tuple return payload unexpectedly short");
        (uint256 actual0, uint256 actual1) = abi.decode(ret, (uint256, uint256));
        assertEq(actual0, expected, "pairWithTotal tuple element 0 should preserve the inferred result");
        assertEq(actual1, (expected + uint256(1)), "pairWithTotal tuple element 1 should preserve the inferred result");
    }
    // Property 4: snapshot decodes and matches the inferred tuple result
    function testAuto_Snapshot_ReturnsInferredTupleResult() public {
        uint256 expected = uint256(1);
        vm.store(target, bytes32(uint256(0)), bytes32(uint256(expected)));
        uint256 expected1 = uint256(1);
        vm.store(target, bytes32(uint256(1)), bytes32(uint256(expected1)));
        uint256 expected2 = uint256(1);
        vm.store(target, bytes32(uint256(2)), bytes32(uint256(expected2)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("snapshot()"));
        require(ok, "snapshot reverted unexpectedly");
        require(ret.length >= 96, "snapshot ABI tuple return payload unexpectedly short");
        (uint256 actual0, uint256 actual1, uint256 actual2) = abi.decode(ret, (uint256, uint256, uint256));
        assertEq(actual0, expected, "snapshot tuple element 0 should preserve the inferred result");
        assertEq(actual1, expected1, "snapshot tuple element 1 should preserve the inferred result");
        assertEq(actual2, expected2, "snapshot tuple element 2 should preserve the inferred result");
    }
}
