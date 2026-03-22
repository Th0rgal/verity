// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

error BadMessage(string message);
error TaggedMessage(uint256 tag, string message);
error SecondMessage(string prefix, string message);

contract StringErrorSmokeReference {
    function checkMessage(bool ok, string calldata message) external pure {
        if (!ok) {
            revert BadMessage(message);
        }
    }

    function checkTaggedMessage(uint256 tag, string calldata message) external pure {
        if (tag != 1) {
            revert TaggedMessage(tag, message);
        }
    }

    function checkSecondMessage(bool ok, string calldata prefix, string calldata message) external pure {
        if (!ok) {
            revert SecondMessage(prefix, message);
        }
    }
}

contract StringErrorSmokeTest is Test, YulTestBase {
    address internal stringErrorSmoke;
    StringErrorSmokeReference internal referenceContract;

    function setUp() public {
        stringErrorSmoke = deployCompiledVerityModule(
            "Contracts.StringErrorSmokeContract",
            "StringErrorSmoke",
            "artifacts/test-string-error-smoke"
        );
        referenceContract = new StringErrorSmokeReference();
    }

    function _assertCheckMessageParity(bool ok, string memory message) internal {
        (bool yulSuccess, bytes memory yulData) =
            stringErrorSmoke.call(abi.encodeWithSignature("checkMessage(bool,string)", ok, message));
        (bool refSuccess, bytes memory refData) =
            address(referenceContract).call(abi.encodeWithSignature("checkMessage(bool,string)", ok, message));

        assertEq(yulSuccess, refSuccess, "success mismatch");
        assertEq(yulData, refData, "revert payload mismatch");
        if (ok) {
            assertTrue(yulSuccess, "expected success");
            assertEq(yulData.length, 0, "successful call should not return data");
        } else {
            assertFalse(yulSuccess, "expected revert");
            assertEq(yulData, abi.encodeWithSelector(BadMessage.selector, message), "custom error ABI mismatch");
        }
    }

    function _assertCheckTaggedMessageParity(uint256 tag, string memory message) internal {
        (bool yulSuccess, bytes memory yulData) =
            stringErrorSmoke.call(abi.encodeWithSignature("checkTaggedMessage(uint256,string)", tag, message));
        (bool refSuccess, bytes memory refData) =
            address(referenceContract).call(abi.encodeWithSignature("checkTaggedMessage(uint256,string)", tag, message));

        assertEq(yulSuccess, refSuccess, "success mismatch");
        assertEq(yulData, refData, "payload mismatch");
        if (tag == 1) {
            assertTrue(yulSuccess, "expected success");
            assertEq(yulData.length, 0, "successful call should not return revert data");
        } else {
            assertFalse(yulSuccess, "expected revert");
            assertEq(yulData, abi.encodeWithSelector(TaggedMessage.selector, tag, message), "custom error ABI mismatch");
        }
    }

    function _assertCheckSecondMessageParity(bool ok, string memory prefix, string memory message) internal {
        (bool yulSuccess, bytes memory yulData) =
            stringErrorSmoke.call(abi.encodeWithSignature("checkSecondMessage(bool,string,string)", ok, prefix, message));
        (bool refSuccess, bytes memory refData) =
            address(referenceContract).call(abi.encodeWithSignature("checkSecondMessage(bool,string,string)", ok, prefix, message));

        assertEq(yulSuccess, refSuccess, "success mismatch");
        assertEq(yulData, refData, "revert payload mismatch");
        if (ok) {
            assertTrue(yulSuccess, "expected success");
            assertEq(yulData.length, 0, "successful call should not return data");
        } else {
            assertFalse(yulSuccess, "expected revert");
            assertEq(
                yulData,
                abi.encodeWithSelector(SecondMessage.selector, prefix, message),
                "custom error ABI mismatch"
            );
        }
    }

    function testCheckMessageSuccessAndRevert() public {
        _assertCheckMessageParity(true, "ok");
        _assertCheckMessageParity(false, unicode"Verity grüßt the 🌍");
    }

    function testCheckTaggedMessageSuccessAndRevert() public {
        _assertCheckTaggedMessageParity(1, "ok");
        _assertCheckTaggedMessageParity(type(uint256).max, "tagged revert payload should preserve the string tail");
    }

    function testCheckSecondMessageTwoDynamicHeads() public {
        _assertCheckSecondMessageParity(true, "", "verity");
        _assertCheckSecondMessageParity(
            false,
            "ignored prefix that still occupies the first dynamic head",
            "the second string should retain its own offset and bytes"
        );
    }
}
