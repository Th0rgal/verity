// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyHelperExternalArgumentSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyHelperExternalArgumentSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("HelperExternalArgumentSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: idWord returns the direct parameter value
    function testAuto_IdWord_ReturnsDirectParam() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("idWord(uint256)", uint256(1)));
        require(ok, "idWord reverted unexpectedly");
        assertEq(ret.length, 32, "idWord ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, uint256(1), "idWord should preserve the expected value");
    }
    // Property 2: pair decodes and matches the inferred tuple result
    function testAuto_Pair_ReturnsInferredTupleResult() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("pair(uint256)", uint256(1)));
        require(ok, "pair reverted unexpectedly");
        require(ret.length >= 64, "pair ABI tuple return payload unexpectedly short");
        (uint256 actual0, uint256 actual1) = abi.decode(ret, (uint256, uint256));
        assertEq(actual0, uint256(1), "pair tuple element 0 should preserve the inferred result");
        assertEq(actual1, 2, "pair tuple element 1 should preserve the inferred result");
    }
    // Property 3: put has no unexpected revert
    function testAuto_Put_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("put(uint256)", uint256(1)));
        require(ok, "put reverted unexpectedly");
    }
    // Property 4: TODO decode and assert `bindExternalArg` result
    function testTODO_BindExternalArg_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("bindExternalArg(uint256)", uint256(1)));
        require(ok, "bindExternalArg reverted unexpectedly");
        assertEq(ret.length, 32, "bindExternalArg ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 5: TODO decode and assert `helperExternalArgRhs` result
    function testTODO_HelperExternalArgRhs_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("helperExternalArgRhs(uint256)", uint256(1)));
        require(ok, "helperExternalArgRhs reverted unexpectedly");
        assertEq(ret.length, 32, "helperExternalArgRhs ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
}
