// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyCEILadderSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyCEILadderSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("CEILadderSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: TODO decode and assert `storeThenCall` result
    function testTODO_StoreThenCall_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("storeThenCall(uint256)", uint256(1)));
        require(ok, "storeThenCall reverted unexpectedly");
        assertEq(ret.length, 32, "storeThenCall ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 2: increment has no unexpected revert
    function testAuto_Increment_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("increment()"));
        require(ok, "increment reverted unexpectedly");
    }
}
