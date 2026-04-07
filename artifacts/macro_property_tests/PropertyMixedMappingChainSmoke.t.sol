// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyMixedMappingChainSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyMixedMappingChainSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("MixedMappingChainSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: setApproval has no unexpected revert
    function testAuto_SetApproval_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("setApproval(address,uint256,address,uint256)", alice, uint256(1), alice, uint256(1)));
        require(ok, "setApproval reverted unexpectedly");
    }
    // Property 2: getApproval reads the configured mapping value
    function testAuto_GetApproval_ReadsConfiguredMapping() public {
        uint256 expected = uint256(1);
        vm.store(target, keccak256(abi.encode(bytes32(uint256(uint160(alice))), keccak256(abi.encode(bytes32(uint256(uint256(1))), _mappingSlot(bytes32(uint256(uint160(alice))), 0))))), bytes32(uint256(expected)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("getApproval(address,uint256,address)", alice, uint256(1), alice));
        require(ok, "getApproval reverted unexpectedly");
        assertEq(ret.length, 32, "getApproval ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, expected, "getApproval should decode the configured mapping value");
    }
}
