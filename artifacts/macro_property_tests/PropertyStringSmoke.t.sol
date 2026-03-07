// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyStringSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/StringSmoke.lean
 */
contract PropertyStringSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("StringSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: TODO decode and assert `echoString` result
    function testTODO_EchoString_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("echoString(string)", "verity"));
        require(ok, "echoString reverted unexpectedly");
        require(ret.length >= 64, "echoString ABI return payload unexpectedly short");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
}
