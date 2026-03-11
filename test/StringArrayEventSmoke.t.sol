// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

contract StringArrayEventSmokeReference {
    event MessageBatch(string[] body, string[] indexed topicBody);

    function logBatch(string[] calldata messages) external {
        emit MessageBatch(messages, messages);
    }
}

contract StringArrayEventSmokeTest is Test, YulTestBase {
    address internal stringArrayEventSmoke;
    StringArrayEventSmokeReference internal referenceContract;

    function setUp() public {
        stringArrayEventSmoke = deployCompiledVerityModule(
            "Contracts.StringArrayEventSmoke",
            "StringArrayEventSmoke",
            "artifacts/test-string-array-event-smoke"
        );
        referenceContract = new StringArrayEventSmokeReference();
    }

    function _assertLogsEqual(Vm.Log[] memory lhs, Vm.Log[] memory rhs) internal pure {
        assertEq(lhs.length, rhs.length, "log count mismatch");
        for (uint256 i = 0; i < lhs.length; i++) {
            assertEq(lhs[i].topics.length, rhs[i].topics.length, "topic count mismatch");
            for (uint256 j = 0; j < lhs[i].topics.length; j++) {
                assertEq(lhs[i].topics[j], rhs[i].topics[j], "topic mismatch");
            }
            assertEq(lhs[i].data, rhs[i].data, "data mismatch");
        }
    }

    function _recordLogs(address target, bytes memory callData) internal returns (Vm.Log[] memory logs) {
        vm.recordLogs();
        (bool ok,) = target.call(callData);
        assertTrue(ok, "event emitter call failed");
        logs = vm.getRecordedLogs();
    }

    function _copyMessages(string[] memory messages) internal pure returns (string[] memory copied) {
        copied = new string[](messages.length);
        for (uint256 i = 0; i < messages.length; i++) {
            copied[i] = messages[i];
        }
    }

    function _assertLogBatchParity(string[] memory messages) internal {
        bytes memory callData = abi.encodeWithSignature("logBatch(string[])", messages);
        Vm.Log[] memory yulLogs = _recordLogs(stringArrayEventSmoke, callData);
        Vm.Log[] memory refLogs = _recordLogs(
            address(referenceContract),
            abi.encodeWithSignature("logBatch(string[])", _copyMessages(messages))
        );
        _assertLogsEqual(yulLogs, refLogs);
    }

    function testLogBatchEmptyArrayParity() public {
        string[] memory messages = new string[](0);
        _assertLogBatchParity(messages);
    }

    function testLogBatchMixedLengthsParity() public {
        string[] memory messages = new string[](4);
        messages[0] = "";
        messages[1] = "verity";
        messages[2] = "0123456789abcdef0123456789abcdef";
        messages[3] = "long nested dynamic payloads should preserve offsets for each string tail";
        _assertLogBatchParity(messages);
    }

    function testLogBatchUtf8Parity() public {
        string[] memory messages = new string[](3);
        messages[0] = unicode"Verity grüßt";
        messages[1] = unicode"nested 🌍 payload";
        messages[2] = unicode"多字节 string[] event";
        _assertLogBatchParity(messages);
    }
}
