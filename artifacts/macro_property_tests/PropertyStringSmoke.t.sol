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

    // Property 1: echoString returns the direct dynamic parameter payload
    function testAuto_EchoString_ReturnsDirectDynamicParam() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("echoString(string)", "verity"));
        require(ok, "echoString reverted unexpectedly");
        require(ret.length >= 64, "echoString ABI return payload unexpectedly short");
        string actual = abi.decode(ret, (string));
        assertEq(actual, "verity", "echoString should preserve the expected value");
    }
    // Property 2: echoStringAfterUint returns the direct dynamic parameter payload
    function testAuto_EchoStringAfterUint_ReturnsDirectDynamicParam() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("echoStringAfterUint(uint256,string)", uint256(1), "verity"));
        require(ok, "echoStringAfterUint reverted unexpectedly");
        require(ret.length >= 64, "echoStringAfterUint ABI return payload unexpectedly short");
        string actual = abi.decode(ret, (string));
        assertEq(actual, "verity", "echoStringAfterUint should preserve the expected value");
    }
    // Property 3: echoStringBeforeUint returns the direct dynamic parameter payload
    function testAuto_EchoStringBeforeUint_ReturnsDirectDynamicParam() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("echoStringBeforeUint(string,uint256)", "verity", uint256(1)));
        require(ok, "echoStringBeforeUint reverted unexpectedly");
        require(ret.length >= 64, "echoStringBeforeUint ABI return payload unexpectedly short");
        string actual = abi.decode(ret, (string));
        assertEq(actual, "verity", "echoStringBeforeUint should preserve the expected value");
    }
    // Property 4: echoSecondString returns the direct dynamic parameter payload
    function testAuto_EchoSecondString_ReturnsDirectDynamicParam() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("echoSecondString(string,string)", "verity", "verity"));
        require(ok, "echoSecondString reverted unexpectedly");
        require(ret.length >= 64, "echoSecondString ABI return payload unexpectedly short");
        string actual = abi.decode(ret, (string));
        assertEq(actual, "verity", "echoSecondString should preserve the expected value");
    }
}
