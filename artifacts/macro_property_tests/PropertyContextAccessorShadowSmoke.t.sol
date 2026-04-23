// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyContextAccessorShadowSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyContextAccessorShadowSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("ContextAccessorShadowSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: echoSenderName returns the direct parameter value
    function testAuto_EchoSenderName_ReturnsDirectParam() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("echoSenderName(address)", alice));
        require(ok, "echoSenderName reverted unexpectedly");
        assertEq(ret.length, 32, "echoSenderName ABI return length mismatch (expected 32 bytes)");
        address actual = abi.decode(ret, (address));
        assertEq(actual, alice, "echoSenderName should preserve the expected value");
    }
    // Property 2: constantNamedChainid returns the declared constant or immutable value
    function testAuto_ConstantNamedChainid_ReturnsDeclaredBinding() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("constantNamedChainid()"));
        require(ok, "constantNamedChainid reverted unexpectedly");
        assertEq(ret.length, 32, "constantNamedChainid ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, 31337, "constantNamedChainid should preserve the expected value");
    }
    // Property 3: immutableNamedBlockTimestamp returns the declared constant or immutable value
    function testAuto_ImmutableNamedBlockTimestamp_ReturnsDeclaredBinding() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("immutableNamedBlockTimestamp()"));
        require(ok, "immutableNamedBlockTimestamp reverted unexpectedly");
        assertEq(ret.length, 32, "immutableNamedBlockTimestamp ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, 12345, "immutableNamedBlockTimestamp should preserve the expected value");
    }
    // Property 4: immutableNamedMsgSender returns the declared constant or immutable value
    function testAuto_ImmutableNamedMsgSender_ReturnsDeclaredBinding() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("immutableNamedMsgSender()"));
        require(ok, "immutableNamedMsgSender reverted unexpectedly");
        assertEq(ret.length, 32, "immutableNamedMsgSender ABI return length mismatch (expected 32 bytes)");
        address actual = abi.decode(ret, (address));
        assertEq(actual, address(uint160(42)), "immutableNamedMsgSender should preserve the expected value");
    }
}
