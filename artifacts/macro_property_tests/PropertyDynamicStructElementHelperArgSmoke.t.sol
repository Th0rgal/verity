// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyDynamicStructElementHelperArgSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyDynamicStructElementHelperArgSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("DynamicStructElementHelperArgSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: TODO decode and assert `consumeValues` result
    function testTODO_ConsumeValues_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("consumeValues(uint256[])", _singletonUintArray(1)));
        require(ok, "consumeValues reverted unexpectedly");
        assertEq(ret.length, 32, "consumeValues ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 2: TODO decode and assert `inspect` result
    function testTODO_Inspect_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("inspect((uint256,uint256[]))", abi.decode(abi.encode(uint256(1), _singletonUintArray(1)), (uint256, uint256[]))));
        require(ok, "inspect reverted unexpectedly");
        assertEq(ret.length, 32, "inspect ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 3: TODO decode and assert `inspectAt` result
    function testTODO_InspectAt_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("inspectAt((uint256,uint256[])[],uint256)", abi.decode(abi.encode(uint256(0)), ((uint256,uint256[])[])), uint256(1)));
        require(ok, "inspectAt reverted unexpectedly");
        assertEq(ret.length, 32, "inspectAt ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }

    function _singletonUintArray(uint256 x) internal pure returns (uint256[] memory arr) {
        arr = new uint256[](1);
        arr[0] = x;
    }
}
