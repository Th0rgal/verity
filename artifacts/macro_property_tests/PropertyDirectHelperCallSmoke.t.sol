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
    // Property 2: TODO decode and assert `readTotalPlus` result
    function testTODO_ReadTotalPlus_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("readTotalPlus(uint256)", uint256(1)));
        require(ok, "readTotalPlus reverted unexpectedly");
        assertEq(ret.length, 32, "readTotalPlus ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 3: TODO decode and assert `pairWithTotal` result
    function testTODO_PairWithTotal_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("pairWithTotal(uint256)", uint256(1)));
        require(ok, "pairWithTotal reverted unexpectedly");
        require(ret.length >= 64, "pairWithTotal ABI tuple return payload unexpectedly short");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 4: TODO decode and assert `runHelpers` result
    function testTODO_RunHelpers_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("runHelpers(uint256,uint256,uint256)", uint256(1), uint256(1), uint256(1)));
        require(ok, "runHelpers reverted unexpectedly");
        assertEq(ret.length, 32, "runHelpers ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 5: TODO decode and assert `snapshot` result
    function testTODO_Snapshot_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("snapshot()"));
        require(ok, "snapshot reverted unexpectedly");
        require(ret.length >= 96, "snapshot ABI tuple return payload unexpectedly short");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
}
