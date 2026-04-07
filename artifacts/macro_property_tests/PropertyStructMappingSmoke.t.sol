// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyStructMappingSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyStructMappingSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("StructMappingSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: setPosition has no unexpected revert
    function testAuto_SetPosition_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("setPosition(address,uint256,uint256,address)", alice, uint256(1), uint256(1), alice));
        require(ok, "setPosition reverted unexpectedly");
    }
    // Property 2: totalPositionShares decodes and matches the inferred straight-line result
    function testAuto_TotalPositionShares_ReturnsInferredStraightLineResult() public {
        uint256 expected = uint256(1);
        uint256 expected1 = uint256(1);
        vm.store(target, _mappingSlot(bytes32(uint256(uint160(alice))), 0), bytes32(uint256(expected) | (uint256(expected1) << 128)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("totalPositionShares(address)", alice));
        require(ok, "totalPositionShares reverted unexpectedly");
        assertEq(ret.length, 32, "totalPositionShares ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, (expected + expected1), "totalPositionShares should preserve the inferred result");
    }
    // Property 3: delegateOf reads the configured struct member
    function testAuto_DelegateOf_ReadsConfiguredStructMember() public {
        address expected = alice;
        vm.store(target, bytes32(uint256(_mappingSlot(bytes32(uint256(uint160(alice))), 0)) + 1), bytes32(uint256(uint160(expected))));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("delegateOf(address)", alice));
        require(ok, "delegateOf reverted unexpectedly");
        assertEq(ret.length, 32, "delegateOf ABI return length mismatch (expected 32 bytes)");
        address actual = abi.decode(ret, (address));
        assertEq(actual, expected, "delegateOf should decode the configured struct member");
    }
    // Property 4: setApproval has no unexpected revert
    function testAuto_SetApproval_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("setApproval(address,address,uint256,uint256)", alice, alice, uint256(1), uint256(1)));
        require(ok, "setApproval reverted unexpectedly");
    }
    // Property 5: approvalOf reads the configured struct member
    function testAuto_ApprovalOf_ReadsConfiguredStructMember() public {
        uint256 expected = uint256(1);
        vm.store(target, _nestedMappingSlot(bytes32(uint256(uint160(alice))), bytes32(uint256(uint160(alice))), 1), bytes32(uint256(expected)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("approvalOf(address,address)", alice, alice));
        require(ok, "approvalOf reverted unexpectedly");
        assertEq(ret.length, 32, "approvalOf ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, expected, "approvalOf should decode the configured struct member");
    }
    // Property 6: approvalNonce reads the configured struct member
    function testAuto_ApprovalNonce_ReadsConfiguredStructMember() public {
        uint256 expected = uint256(1);
        vm.store(target, bytes32(uint256(_nestedMappingSlot(bytes32(uint256(uint160(alice))), bytes32(uint256(uint160(alice))), 1)) + 1), bytes32(uint256(expected)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("approvalNonce(address,address)", alice, alice));
        require(ok, "approvalNonce reverted unexpectedly");
        assertEq(ret.length, 32, "approvalNonce ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, expected, "approvalNonce should decode the configured struct member");
    }
}
