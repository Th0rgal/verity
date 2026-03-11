// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

error BadMessages(string[] messages);
error TaggedMessages(uint256 tag, string[] messages);
error SecondMessages(string[] prefix, string[] messages);

contract StringArrayErrorSmokeReference {
    function checkBatch(bool ok, string[] calldata messages) external pure {
        if (!ok) {
            revert BadMessages(messages);
        }
    }

    function checkTaggedBatch(uint256 tag, string[] calldata messages) external pure {
        if (tag != 1) {
            revert TaggedMessages(tag, messages);
        }
    }

    function checkSecondBatch(bool ok, string[] calldata prefix, string[] calldata messages) external pure {
        if (!ok) {
            revert SecondMessages(prefix, messages);
        }
    }
}

contract StringArrayErrorSmokeTest is Test, YulTestBase {
    address internal stringArrayErrorSmoke;
    StringArrayErrorSmokeReference internal referenceContract;

    function setUp() public {
        stringArrayErrorSmoke = deployCompiledVerityModule(
            "Contracts.StringArrayErrorSmoke",
            "StringArrayErrorSmoke",
            "artifacts/test-string-array-error-smoke"
        );
        referenceContract = new StringArrayErrorSmokeReference();
    }

    function _copyMessages(string[] memory messages) internal pure returns (string[] memory copied) {
        copied = new string[](messages.length);
        for (uint256 i = 0; i < messages.length; i++) {
            copied[i] = messages[i];
        }
    }

    function _assertCheckBatchParity(bool ok, string[] memory messages) internal {
        (bool yulSuccess, bytes memory yulData) =
            stringArrayErrorSmoke.call(abi.encodeWithSignature("checkBatch(bool,string[])", ok, messages));
        (bool refSuccess, bytes memory refData) =
            address(referenceContract).call(
                abi.encodeWithSignature("checkBatch(bool,string[])", ok, _copyMessages(messages))
            );

        assertEq(yulSuccess, refSuccess, "success mismatch");
        assertEq(yulData, refData, "revert payload mismatch");
        if (ok) {
            assertTrue(yulSuccess, "expected success");
            assertEq(yulData.length, 0, "successful call should not return data");
        } else {
            assertFalse(yulSuccess, "expected revert");
            assertEq(
                yulData,
                abi.encodeWithSelector(BadMessages.selector, _copyMessages(messages)),
                "custom error ABI mismatch"
            );
        }
    }

    function _assertCheckTaggedBatchParity(uint256 tag, string[] memory messages) internal {
        (bool yulSuccess, bytes memory yulData) =
            stringArrayErrorSmoke.call(abi.encodeWithSignature("checkTaggedBatch(uint256,string[])", tag, messages));
        (bool refSuccess, bytes memory refData) = address(referenceContract).call(
            abi.encodeWithSignature("checkTaggedBatch(uint256,string[])", tag, _copyMessages(messages))
        );

        assertEq(yulSuccess, refSuccess, "success mismatch");
        assertEq(yulData, refData, "revert payload mismatch");
        if (tag == 1) {
            assertTrue(yulSuccess, "expected success");
            assertEq(yulData.length, 0, "successful call should not return data");
        } else {
            assertFalse(yulSuccess, "expected revert");
            assertEq(
                yulData,
                abi.encodeWithSelector(TaggedMessages.selector, tag, _copyMessages(messages)),
                "custom error ABI mismatch"
            );
        }
    }

    function _assertCheckSecondBatchParity(bool ok, string[] memory prefix, string[] memory messages) internal {
        (bool yulSuccess, bytes memory yulData) = stringArrayErrorSmoke.call(
            abi.encodeWithSignature("checkSecondBatch(bool,string[],string[])", ok, prefix, messages)
        );
        (bool refSuccess, bytes memory refData) = address(referenceContract).call(
            abi.encodeWithSignature(
                "checkSecondBatch(bool,string[],string[])",
                ok,
                _copyMessages(prefix),
                _copyMessages(messages)
            )
        );

        assertEq(yulSuccess, refSuccess, "success mismatch");
        assertEq(yulData, refData, "revert payload mismatch");
        if (ok) {
            assertTrue(yulSuccess, "expected success");
            assertEq(yulData.length, 0, "successful call should not return data");
        } else {
            assertFalse(yulSuccess, "expected revert");
            assertEq(
                yulData,
                abi.encodeWithSelector(SecondMessages.selector, _copyMessages(prefix), _copyMessages(messages)),
                "custom error ABI mismatch"
            );
        }
    }

    function testCheckBatchParity() public {
        string[] memory emptyMessages = new string[](0);
        _assertCheckBatchParity(true, emptyMessages);

        string[] memory messages = new string[](4);
        messages[0] = "";
        messages[1] = "verity";
        messages[2] = "0123456789abcdef0123456789abcdef";
        messages[3] = "string[] custom errors should preserve nested dynamic tails";
        _assertCheckBatchParity(false, messages);
    }

    function testCheckTaggedBatchParity() public {
        string[] memory okMessages = new string[](1);
        okMessages[0] = "ok";
        _assertCheckTaggedBatchParity(1, okMessages);

        string[] memory messages = new string[](3);
        messages[0] = unicode"Verity grüßt";
        messages[1] = unicode"nested 🌍 payload";
        messages[2] = unicode"多字节 string[] error";
        _assertCheckTaggedBatchParity(type(uint256).max, messages);
    }

    function testCheckSecondBatchParity() public {
        string[] memory prefix = new string[](2);
        prefix[0] = "first dynamic head";
        prefix[1] = "still shifts the second array offsets";

        string[] memory messages = new string[](3);
        messages[0] = "";
        messages[1] = "second dynamic head";
        messages[2] = "should preserve each nested string payload";

        _assertCheckSecondBatchParity(false, prefix, messages);
    }
}
