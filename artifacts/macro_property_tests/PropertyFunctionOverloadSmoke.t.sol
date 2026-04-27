// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyFunctionOverloadSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyFunctionOverloadSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("FunctionOverloadSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: echo returns the direct parameter value
    function testAuto_Echo_ReturnsDirectParam() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("echo(uint256)", uint256(1)));
        require(ok, "echo reverted unexpectedly");
        assertEq(ret.length, 32, "echo ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, uint256(1), "echo should preserve the expected value");
    }
    // Property 2: TODO decode and assert `echo` result
    function testTODO_Echo_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("echo(address)", alice));
        require(ok, "echo reverted unexpectedly");
        assertEq(ret.length, 32, "echo ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 3: echo returns the declared constant result
    function testAuto_Echo_ReturnsDeclaredConstant() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("echo(uint256,uint256)", uint256(1), uint256(1)));
        require(ok, "echo reverted unexpectedly");
        assertEq(ret.length, 32, "echo ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, 2, "echo should return the declared constant");
    }
}
