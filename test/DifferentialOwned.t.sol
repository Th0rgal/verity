// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import {console2} from "forge-std/Test.sol";
import "./DiffTestConfig.sol";
import "./yul/YulTestBase.sol";

/**
 * @title DifferentialOwned
 * @notice Differential testing for Owned contract
 *
 * Approach:
 * 1. Generate random transactions (transferOwnership, getOwner)
 * 2. Execute on compiled Yul contract (EVM)
 * 3. Execute on EDSL interpreter (via vm.ffi)
 * 4. Assert identical results (owner address storage)
 *
 * Success: 100+ tests with zero mismatches
 */
contract DifferentialOwned is YulTestBase, DiffTestConfig {
    // Compiled contract
    address owned;

    // Test counters
    uint256 public testsPassed;
    uint256 public testsFailed;

    // Storage state tracking for EDSL interpreter
    mapping(uint256 => address) edslStorageAddr;  // Slot 0: owner address

    function setUp() public {
        // Deploy Owned from Yul with constructor arg (initialOwner)
        address initialOwner = address(this);
        owned = deployYulWithArgs("Owned", abi.encode(initialOwner));
        require(owned != address(0), "Deploy failed");

        // Set EDSL state
        edslStorageAddr[0] = initialOwner;
    }

    /**
     * @notice Execute transaction on EVM and EDSL, compare results
     */
    function executeDifferentialTest(
        string memory functionName,
        address sender,
        uint256 arg0
    ) internal returns (bool success) {
        // 1. Execute on compiled contract (EVM)
        vm.prank(sender);

        bool evmSuccess;
        bytes memory evmReturnData;

        bytes32 functionSig = keccak256(bytes(functionName));

        if (functionSig == keccak256(bytes("transferOwnership"))) {
            (evmSuccess, evmReturnData) = owned.call(
                abi.encodeWithSignature("transferOwnership(address)", address(uint160(arg0)))
            );
        } else if (functionSig == keccak256(bytes("getOwner"))) {
            (evmSuccess, evmReturnData) = owned.call(
                abi.encodeWithSignature("getOwner()")
            );
        } else {
            revert("Unknown function");
        }

        address evmOwnerAfter = address(uint160(uint256(vm.load(owned, bytes32(uint256(0))))));  // owner at slot 0
        address evmReturnAddress = address(0);

        if (evmReturnData.length > 0) {
            if (functionSig == keccak256(bytes("getOwner"))) {
                evmReturnAddress = abi.decode(evmReturnData, (address));
            }
        }

        // 2. Execute on EDSL interpreter (via vm.ffi)
        string memory storageState = _buildStorageString();
        string memory edslResult = _runInterpreter(functionName, sender, arg0, storageState);

        // 3. Parse and compare results
        bool verbose = _diffVerbose();
        if (verbose) {
            console2.log("Function:", functionName);
            console2.log("EVM success:", evmSuccess);
            console2.log("EVM owner:", evmOwnerAfter);
            console2.log("EDSL result:", edslResult);
        }

        // Parse EDSL result
        bool edslSuccess = contains(edslResult, "\"success\":true");

        // Validate JSON structure
        if (!contains(edslResult, "\"returnValue\":")) {
            console2.log("ERROR: Malformed JSON - missing returnValue field");
            console2.log("  JSON:", edslResult);
            testsFailed++;
            return false;
        }

        uint256 edslReturnValue = _extractReturnValue(edslResult);

        // Validate: Success flags must match
        if (evmSuccess != edslSuccess) {
            console2.log("MISMATCH: Success flags differ!");
            console2.log("  EVM:", evmSuccess);
            console2.log("  EDSL:", edslSuccess);
            testsFailed++;
            return false;
        }

        // Validate: Return values must match (for getOwner)
        if (functionSig == keccak256(bytes("getOwner"))) {
            // For getOwner, compare address returned vs stored in EDSL
            if (uint256(uint160(evmReturnAddress)) != edslReturnValue) {
                console2.log("MISMATCH: Owner addresses differ!");
                console2.log("  EVM:", evmReturnAddress);
                console2.log("  EDSL:", address(uint160(edslReturnValue)));
                testsFailed++;
                return false;
            }
        }

        // Validate: Storage must match
        // Parse storage changes from EDSL (address storage)
        if (contains(edslResult, "\"storageAddrChanges\":[")) {
            _extractStorageAddrChanges(edslResult);
        }

        // Compare owner address
        if (uint256(uint160(evmOwnerAfter)) != uint256(uint160(edslStorageAddr[0]))) {
            console2.log("MISMATCH: Owner storage differs!");
            console2.log("  EVM owner:", evmOwnerAfter);
            console2.log("  EDSL owner:", edslStorageAddr[0]);
            testsFailed++;
            return false;
        }

        testsPassed++;
        return true;
    }

    /**
     * @notice Build storage string for EDSL interpreter
     */
    function _buildStorageString() internal view returns (string memory) {
        // Format: "addr=0:address" for owner at slot 0
        // Need "addr=" prefix to distinguish from regular storage
        return string(abi.encodePacked(
            "addr=0:",
            _addressToString(edslStorageAddr[0])
        ));
    }

    /**
     * @notice Run EDSL interpreter via vm.ffi
     */
    function _runInterpreter(
        string memory functionName,
        address sender,
        uint256 arg0,
        string memory storageState
    ) internal returns (string memory) {
        // Format: contractType functionName senderAddr [args...] [storage]
        // For transferOwnership: arg0 is the new owner address (as Nat)
        // For getOwner: no args

        bytes32 functionSig = keccak256(bytes(functionName));

        string memory baseCmd = string.concat(
            "cd \"$(git rev-parse --show-toplevel)\" && export PATH=\"$HOME/.elan/bin:$PATH\" && ",
            "if [ ! -x ./.lake/build/bin/difftest-interpreter ]; then ",
            "mkdir -p .lake/build/bin && lake build difftest-interpreter >/dev/null; ",
            "fi; ",
            "./.lake/build/bin/difftest-interpreter",
            " Owned ",
            functionName,
            " ",
            _addressToString(sender)
        );

        if (functionSig == keccak256(bytes("transferOwnership"))) {
            string memory cmd = string.concat(
                baseCmd,
                " ",
                _uint256ToString(arg0)
            );
            if (bytes(storageState).length > 0) {
                cmd = string.concat(cmd, " \"", storageState, "\"");
            }
            cmd = string.concat(cmd, " value=0 timestamp=", vm.toString(block.timestamp));
            string[] memory inputs = new string[](3);
            inputs[0] = "bash";
            inputs[1] = "-c";
            inputs[2] = cmd;
            bytes memory result = vm.ffi(inputs);
            return string(result);
        } else {
            string memory cmd = baseCmd;
            if (bytes(storageState).length > 0) {
                cmd = string.concat(cmd, " \"", storageState, "\"");
            }
            cmd = string.concat(cmd, " value=0 timestamp=", vm.toString(block.timestamp));
            string[] memory inputs = new string[](3);
            inputs[0] = "bash";
            inputs[1] = "-c";
            inputs[2] = cmd;
            bytes memory result = vm.ffi(inputs);
            return string(result);
        }
    }

    /**
     * @notice Extract storageAddrChanges from JSON result
     */
    function _extractStorageAddrChanges(string memory json) internal {
        bytes memory jsonBytes = bytes(json);
        uint256 storageAddrStart = _indexOf(jsonBytes, bytes("\"storageAddrChanges\":["));
        if (storageAddrStart == type(uint256).max) return;

        // Find the array content between [ and ]
        uint256 arrayStart = storageAddrStart + bytes("\"storageAddrChanges\":[").length;
        uint256 arrayEnd = arrayStart;
        uint256 bracketDepth = 1;

        for (uint256 i = arrayStart; i < jsonBytes.length && bracketDepth > 0; i++) {
            if (jsonBytes[i] == '[') bracketDepth++;
            if (jsonBytes[i] == ']') {
                bracketDepth--;
                if (bracketDepth == 0) {
                    arrayEnd = i;
                    break;
                }
            }
        }

        // Extract array content
        bytes memory arrayContent = new bytes(arrayEnd - arrayStart);
        for (uint256 i = 0; i < arrayEnd - arrayStart; i++) {
            arrayContent[i] = jsonBytes[arrayStart + i];
        }

        // Parse each change object: {"slot":N,"value":"address"}
        if (arrayContent.length > 2) {  // More than just []
            _parseStorageAddrArray(arrayContent);
        }
    }

    /**
     * @notice Parse storage address array
     */
    function _parseStorageAddrArray(bytes memory arrayContent) internal {
        // Split by },{
        uint256 start = 0;
        for (uint256 i = 0; i < arrayContent.length; i++) {
            if (i > 0 && arrayContent[i] == '{' && arrayContent[i-1] == ',') {
                bytes memory obj = _extractBytes(arrayContent, start, i - 1);
                _parseStorageAddrObject(obj);
                start = i;
            }
        }
        // Parse last object
        if (start < arrayContent.length) {
            bytes memory obj = _extractBytes(arrayContent, start, arrayContent.length);
            _parseStorageAddrObject(obj);
        }
    }

    /**
     * @notice Parse single storage address change object
     */
    function _parseStorageAddrObject(bytes memory obj) internal {
        // Extract slot: "slot":N
        uint256 slotStart = _indexOf(obj, bytes("\"slot\":"));
        if (slotStart == type(uint256).max) return;
        slotStart += bytes("\"slot\":").length;
        uint256 slotEnd = slotStart;
        while (slotEnd < obj.length && obj[slotEnd] >= '0' && obj[slotEnd] <= '9') {
            slotEnd++;
        }
        bytes memory slotBytes = _extractBytes(obj, slotStart, slotEnd);
        uint256 slot = _stringToUint(string(slotBytes));

        // Extract value: "value":"..." or "value":decimal
        uint256 valueStart = _indexOf(obj, bytes("\"value\":"));
        if (valueStart == type(uint256).max) return;
        valueStart += bytes("\"value\":").length;

        // Skip whitespace
        while (valueStart < obj.length && (obj[valueStart] == ' ' || obj[valueStart] == '\t')) {
            valueStart++;
        }

        bytes memory valueBytes;
        if (obj[valueStart] == '"') {
            // String value
            valueStart++;
            uint256 valueEnd = valueStart;
            while (valueEnd < obj.length && obj[valueEnd] != '"') {
                valueEnd++;
            }
            valueBytes = _extractBytes(obj, valueStart, valueEnd);
        } else {
            // Numeric value (decimal or hex)
            uint256 valueEnd = valueStart;
            while (valueEnd < obj.length &&
                   ((obj[valueEnd] >= '0' && obj[valueEnd] <= '9') ||
                    (obj[valueEnd] >= 'a' && obj[valueEnd] <= 'f') ||
                    (obj[valueEnd] >= 'A' && obj[valueEnd] <= 'F') ||
                    obj[valueEnd] == 'x')) {
                valueEnd++;
            }
            valueBytes = _extractBytes(obj, valueStart, valueEnd);
        }

        // Parse value (try hex first, then decimal)
        string memory valueStr = string(valueBytes);
        uint256 addrNat;
        if (valueBytes.length >= 2 && valueBytes[0] == '0' &&
            (valueBytes[1] == 'x' || valueBytes[1] == 'X')) {
            addrNat = _parseHexAddress(valueStr);
        } else {
            // Parse as decimal
            addrNat = _stringToUint(valueStr);
        }

        // Update EDSL storage
        edslStorageAddr[slot] = address(uint160(addrNat));
    }

    /**
     * @notice Parse hex address string to uint256
     */
    function _parseHexAddress(string memory hexStr) internal pure returns (uint256) {
        bytes memory hexBytes = bytes(hexStr);
        require(hexBytes.length >= 2 && hexBytes[0] == '0' &&
                (hexBytes[1] == 'x' || hexBytes[1] == 'X'), "Invalid hex");

        uint256 result = 0;
        for (uint256 i = 2; i < hexBytes.length; i++) {
            result = result * 16;
            uint8 digit = uint8(hexBytes[i]);
            if (digit >= 48 && digit <= 57) {
                result += digit - 48;  // 0-9
            } else if (digit >= 65 && digit <= 70) {
                result += digit - 55;  // A-F
            } else if (digit >= 97 && digit <= 102) {
                result += digit - 87;  // a-f
            }
        }
        return result;
    }

    // ========== Test Cases ==========

    /**
     * @notice Test: Basic ownership transfer
     */
    function testDifferential_TransferOwnership() public {
        address newOwner = address(0xa11ce);

        bool success = executeDifferentialTest("transferOwnership", address(this), uint256(uint160(newOwner)));
        require(success, "Test failed");

        // Verify owner changed
        bool success2 = executeDifferentialTest("getOwner", address(this), 0);
        require(success2, "Test failed");
    }

    /**
     * @notice Test: Access control (non-owner cannot transfer)
     */
    function testDifferential_AccessControl() public {
        address nonOwner = address(0xb0b);
        address newOwner = address(0xa11ce);

        // This should fail (revert)
        bool success = executeDifferentialTest("transferOwnership", nonOwner, uint256(uint160(newOwner)));
        require(success, "Test failed");  // success means EVM and EDSL both reverted

        // Owner should remain unchanged
        bool success2 = executeDifferentialTest("getOwner", address(this), 0);
        require(success2, "Test failed");
    }

    /**
     * @notice Test: Get owner operation
     */
    function testDifferential_GetOwner() public {
        bool success = executeDifferentialTest("getOwner", address(this), 0);
        require(success, "Test failed");
    }

    /**
     * @notice Test: Multiple ownership transfers
     */
    function testDifferential_MultipleTransfers() public {
        address alice = address(0xa11ce);
        address bob = address(0xb0b);

        // Transfer to Alice
        bool success1 = executeDifferentialTest("transferOwnership", address(this), uint256(uint160(alice)));
        require(success1, "Test 1 failed");

        // Transfer to Bob (as Alice)
        bool success2 = executeDifferentialTest("transferOwnership", alice, uint256(uint160(bob)));
        require(success2, "Test 2 failed");

        // Verify final owner is Bob
        bool success3 = executeDifferentialTest("getOwner", address(this), 0);
        require(success3, "Test 3 failed");
    }

    /**
     * @notice Test: Random transactions (100+)
     */
    function testDifferential_Random100() public {
        // Deterministic PRNG seed for reproducibility
        (uint256 startIndex, uint256 numTransactions) = _diffRandomSmallRange();
        uint256 seed = _diffRandomSeed("Owned");

        address[] memory testAddresses = new address[](5);
        testAddresses[0] = address(this);
        testAddresses[1] = address(0xa11ce);
        testAddresses[2] = address(0xb0b);
        testAddresses[3] = address(0xCA401);
        testAddresses[4] = address(0xDABE);

        console2.log("Generated", numTransactions, "random transactions");

        seed = _skipRandom(seed, startIndex);
        for (uint256 i = 0; i < numTransactions; i++) {
            seed = _lcg(seed);
            uint256 txType = seed % 100;

            address sender;
            uint256 arg0;

            if (txType < 60) {
                // 60% transferOwnership
                sender = edslStorageAddr[0];  // Current owner
                seed = _lcg(seed);
                arg0 = uint256(uint160(testAddresses[seed % testAddresses.length]));

                bool success = executeDifferentialTest("transferOwnership", sender, arg0);
                _assertRandomSuccess(success, startIndex + i);
            } else {
                // 40% getOwner
                seed = _lcg(seed);
                sender = testAddresses[seed % testAddresses.length];
                arg0 = 0;

                bool success = executeDifferentialTest("getOwner", sender, arg0);
                _assertRandomSuccess(success, startIndex + i);
            }
        }

        console2.log("All random tests passed!");
        console2.log("Tests passed:", testsPassed);
        console2.log("Tests failed:", testsFailed);
        require(testsFailed == 0, "Some tests failed");
    }

    /**
     * @notice Test: Random transactions (1000+)
     */
    function testDifferential_Random10000() public {
        // Deterministic PRNG seed for reproducibility
        (uint256 startIndex, uint256 numTransactions) = _diffRandomLargeRange();
        uint256 seed = _diffRandomSeed("Owned");

        address[] memory testAddresses = new address[](5);
        testAddresses[0] = address(this);
        testAddresses[1] = address(0xa11ce);
        testAddresses[2] = address(0xb0b);
        testAddresses[3] = address(0xCA401);
        testAddresses[4] = address(0xDABE);

        console2.log("Generated", numTransactions, "random transactions");

        seed = _skipRandom(seed, startIndex);
        for (uint256 i = 0; i < numTransactions; i++) {
            seed = _lcg(seed);
            uint256 txType = seed % 100;

            address sender;
            uint256 arg0;

            if (txType < 60) {
                // 60% transferOwnership
                sender = edslStorageAddr[0];  // Current owner
                seed = _lcg(seed);
                arg0 = uint256(uint160(testAddresses[seed % testAddresses.length]));

                bool success = executeDifferentialTest("transferOwnership", sender, arg0);
                _assertRandomSuccess(success, startIndex + i);
            } else {
                // 40% getOwner
                seed = _lcg(seed);
                sender = testAddresses[seed % testAddresses.length];
                arg0 = 0;

                bool success = executeDifferentialTest("getOwner", sender, arg0);
                _assertRandomSuccess(success, startIndex + i);
            }
        }

        console2.log("All random tests passed!");
        console2.log("Tests passed:", testsPassed);
        console2.log("Tests failed:", testsFailed);
        require(testsFailed == 0, "Some tests failed");
    }

    // ========== Helper Functions ==========

    function _skipRandom(uint256 seed, uint256 iterations) internal pure returns (uint256) {
        for (uint256 i = 0; i < iterations; i++) {
            seed = _lcg(seed);
            seed = _lcg(seed);
        }
        return seed;
    }

    /**
     * @notice Extract return value from JSON
     */
    function _extractReturnValue(string memory json) internal pure returns (uint256) {
        bytes memory jsonBytes = bytes(json);
        uint256 start = _indexOf(jsonBytes, bytes("\"returnValue\":"));
        if (start == type(uint256).max) return 0;

        start += bytes("\"returnValue\":").length;

        // Skip whitespace and quotes
        while (start < jsonBytes.length && (jsonBytes[start] == ' ' || jsonBytes[start] == '"')) {
            start++;
        }

        uint256 end = start;
        while (end < jsonBytes.length && jsonBytes[end] >= '0' && jsonBytes[end] <= '9') {
            end++;
        }

        bytes memory numBytes = new bytes(end - start);
        for (uint256 i = 0; i < end - start; i++) {
            numBytes[i] = jsonBytes[start + i];
        }

        return _stringToUint(string(numBytes));
    }

    /**
     * @notice Convert address to lowercase hex string
     */
    function _addressToString(address addr) internal pure returns (string memory) {
        bytes memory result = new bytes(42);
        result[0] = '0';
        result[1] = 'x';

        bytes20 addrBytes = bytes20(addr);
        for (uint256 i = 0; i < 20; i++) {
            uint8 b = uint8(addrBytes[i]);
            result[2 + i*2] = _hexChar(b >> 4);
            result[3 + i*2] = _hexChar(b & 0x0f);
        }

        return string(result);
    }

    /**
     * @notice Convert hex digit to lowercase char
     */
    function _hexChar(uint8 value) internal pure returns (bytes1) {
        if (value < 10) {
            return bytes1(uint8(48 + value));  // 0-9
        } else {
            return bytes1(uint8(87 + value));  // a-f (lowercase)
        }
    }

    /**
     * @notice Convert uint256 to string
     */
    function _uint256ToString(uint256 value) internal pure returns (string memory) {
        if (value == 0) {
            return "0";
        }

        uint256 temp = value;
        uint256 digits;
        while (temp != 0) {
            digits++;
            temp /= 10;
        }

        bytes memory buffer = new bytes(digits);
        while (value != 0) {
            digits -= 1;
            buffer[digits] = bytes1(uint8(48 + uint256(value % 10)));
            value /= 10;
        }

        return string(buffer);
    }

    /**
     * @notice Convert string to uint256
     */
    function _stringToUint(string memory s) internal pure returns (uint256) {
        bytes memory b = bytes(s);
        uint256 result = 0;
        for (uint256 i = 0; i < b.length; i++) {
            uint8 digit = uint8(b[i]);
            if (digit >= 48 && digit <= 57) {
                unchecked { result = result * 10 + (digit - 48); }
            }
        }
        return result;
    }

    /**
     * @notice Find substring index in bytes
     */
    function _indexOf(bytes memory haystack, bytes memory needle) internal pure returns (uint256) {
        if (needle.length > haystack.length) return type(uint256).max;

        for (uint256 i = 0; i <= haystack.length - needle.length; i++) {
            bool found = true;
            for (uint256 j = 0; j < needle.length; j++) {
                if (haystack[i + j] != needle[j]) {
                    found = false;
                    break;
                }
            }
            if (found) return i;
        }

        return type(uint256).max;
    }

    /**
     * @notice Extract bytes slice
     */
    function _extractBytes(bytes memory data, uint256 start, uint256 end) internal pure returns (bytes memory) {
        require(end >= start && end <= data.length, "Invalid range");
        bytes memory result = new bytes(end - start);
        for (uint256 i = 0; i < end - start; i++) {
            result[i] = data[start + i];
        }
        return result;
    }

    /**
     * @notice Check if string contains substring
     */
    function contains(string memory haystack, string memory needle) internal pure returns (bool) {
        return _indexOf(bytes(haystack), bytes(needle)) != type(uint256).max;
    }
}
