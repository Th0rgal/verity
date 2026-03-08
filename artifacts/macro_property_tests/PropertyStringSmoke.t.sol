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
    // Property 2: TODO decode and assert `echoStringAfterUint` result
    function testTODO_EchoStringAfterUint_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("echoStringAfterUint(uint256,string)", uint256(1), "verity"));
        require(ok, "echoStringAfterUint reverted unexpectedly");
        require(ret.length >= 64, "echoStringAfterUint ABI return payload unexpectedly short");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 3: TODO decode and assert `echoStringBeforeUint` result
    function testTODO_EchoStringBeforeUint_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("echoStringBeforeUint(string,uint256)", "verity", uint256(1)));
        require(ok, "echoStringBeforeUint reverted unexpectedly");
        require(ret.length >= 64, "echoStringBeforeUint ABI return payload unexpectedly short");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 4: TODO decode and assert `echoSecondString` result
    function testTODO_EchoSecondString_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("echoSecondString(string,string)", "verity", "verity"));
        require(ok, "echoSecondString reverted unexpectedly");
        require(ret.length >= 64, "echoSecondString ABI return payload unexpectedly short");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
}
