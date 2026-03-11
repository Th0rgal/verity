// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyStringEqSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/StringSmoke.lean
 */
contract PropertyStringEqSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("StringEqSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: TODO decode and assert `same` result
    function testTODO_Same_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("same(string,string)", "verity", "verity"));
        require(ok, "same reverted unexpectedly");
        assertEq(ret.length, 32, "same ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 2: TODO decode and assert `different` result
    function testTODO_Different_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("different(string,string)", "verity", "verity"));
        require(ok, "different reverted unexpectedly");
        assertEq(ret.length, 32, "different ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 3: TODO decode and assert `choose` result
    function testTODO_Choose_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("choose(string,string)", "verity", "verity"));
        require(ok, "choose reverted unexpectedly");
        assertEq(ret.length, 32, "choose ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
}
