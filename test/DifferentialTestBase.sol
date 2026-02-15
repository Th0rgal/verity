// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import {console2} from "forge-std/Test.sol";

/**
 * @title DifferentialTestBase
 * @notice Shared utilities for differential testing contracts
 *
 * Provides common JSON parsing, string manipulation, and storage handling
 * functions used across all differential test suites.
 */
abstract contract DifferentialTestBase {
    // Test counters (derived contracts can use these)
    uint256 public testsPassed;
    uint256 public testsFailed;

    /**
     * @notice Check if string contains substring
     */
    function contains(string memory str, string memory substr) internal pure returns (bool) {
        bytes memory strBytes = bytes(str);
        bytes memory substrBytes = bytes(substr);

        if (substrBytes.length > strBytes.length) return false;

        for (uint i = 0; i <= strBytes.length - substrBytes.length; i++) {
            bool found = true;
            for (uint j = 0; j < substrBytes.length; j++) {
                if (strBytes[i + j] != substrBytes[j]) {
                    found = false;
                    break;
                }
            }
            if (found) return true;
        }
        return false;
    }

    /**
     * @notice Extract returnValue from EDSL JSON response
     * @dev Expects format: {"returnValue":"123",...}
     *      The value is quoted in the JSON output
     */
    function _extractReturnValue(string memory json) internal pure returns (uint256) {
        bytes memory jsonBytes = bytes(json);
        bytes memory searchBytes = bytes("\"returnValue\":\"");

        if (jsonBytes.length < searchBytes.length) return 0;

        // Find "returnValue":"
        for (uint i = 0; i <= jsonBytes.length - searchBytes.length; i++) {
            bool found = true;
            for (uint j = 0; j < searchBytes.length; j++) {
                if (jsonBytes[i + j] != searchBytes[j]) {
                    found = false;
                    break;
                }
            }
            if (found) {
                // Extract the value between the quotes
                uint start = i + searchBytes.length;
                uint end = start;
                while (end < jsonBytes.length && jsonBytes[end] != bytes1('"')) {
                    end++;
                }
                bytes memory numBytes = new bytes(end - start);
                for (uint k = 0; k < end - start; k++) {
                    numBytes[k] = jsonBytes[start + k];
                }
                return _stringToUint(string(numBytes));
            }
        }
        return 0;
    }

    /**
     * @notice Extract storage change from EDSL JSON response
     * @dev Expects format: {"storageChanges":[{"slot":X,"value":Y},...]}
     *      Storage changes are array of objects, not nested arrays
     */
    function _extractStorageChange(string memory json, uint256 slot)
        internal
        pure
        returns (bool found, uint256 value)
    {
        bytes memory jsonBytes = bytes(json);
        bytes memory slotPattern = bytes(string.concat("\"slot\":", _uintToString(slot)));

        if (jsonBytes.length < slotPattern.length) return (false, 0);

        // Find "slot":X
        for (uint i = 0; i <= jsonBytes.length - slotPattern.length; i++) {
            bool foundSlot = true;
            for (uint j = 0; j < slotPattern.length; j++) {
                if (jsonBytes[i + j] != slotPattern[j]) {
                    foundSlot = false;
                    break;
                }
            }
            if (foundSlot) {
                // Now find "value": in the same object
                bytes memory valuePattern = bytes("\"value\":");
                if (jsonBytes.length < valuePattern.length) return (false, 0);

                for (uint k = i; k <= jsonBytes.length - valuePattern.length; k++) {
                    bool foundValue = true;
                    for (uint l = 0; l < valuePattern.length; l++) {
                        if (jsonBytes[k + l] != valuePattern[l]) {
                            foundValue = false;
                            break;
                        }
                    }
                    if (foundValue) {
                        // Extract the numeric value after "value":
                        uint start = k + valuePattern.length;
                        uint end = start;
                        // Parse digits (value is not quoted)
                        while (end < jsonBytes.length && jsonBytes[end] >= 0x30 && jsonBytes[end] <= 0x39) {
                            end++;
                        }
                        bytes memory numBytes = new bytes(end - start);
                        for (uint m = 0; m < end - start; m++) {
                            numBytes[m] = jsonBytes[start + m];
                        }
                        return (true, _stringToUint(string(numBytes)));
                    }
                }
            }
        }
        return (false, 0);
    }

    /**
     * @notice Convert uint256 to string
     * @param value The uint256 to convert
     * @return The string representation
     */
    function _uintToString(uint256 value) internal pure returns (string memory) {
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
     * @notice Parse a number from JSON starting at given index
     */
    function _extractNumber(string memory json, uint256 startIdx) internal pure returns (uint256) {
        bytes memory b = bytes(json);
        uint256 result = 0;
        uint256 i = startIdx;

        // Skip whitespace
        while (i < b.length && (b[i] == " " || b[i] == "\t" || b[i] == "\n")) {
            i++;
        }

        // Parse digits
        while (i < b.length && b[i] >= "0" && b[i] <= "9") {
            result = result * 10 + uint8(b[i]) - uint8(bytes1("0"));
            i++;
        }

        return result;
    }

    /**
     * @notice Convert string to uint256
     */
    function _stringToUint(string memory s) internal pure returns (uint256) {
        bytes memory b = bytes(s);
        uint256 result = 0;

        for (uint i = 0; i < b.length; i++) {
            if (b[i] >= "0" && b[i] <= "9") {
                result = result * 10 + (uint8(b[i]) - uint8(bytes1("0")));
            }
        }

        return result;
    }

    /**
     * @notice Convert string to lowercase
     */
    function _toLowerCase(string memory str) internal pure returns (string memory) {
        bytes memory b = bytes(str);
        bytes memory result = new bytes(b.length);

        for (uint i = 0; i < b.length; i++) {
            if (b[i] >= "A" && b[i] <= "Z") {
                result[i] = bytes1(uint8(b[i]) + 32);
            } else {
                result[i] = b[i];
            }
        }

        return string(result);
    }

    /**
     * @notice Convert index to deterministic address
     */
    function _indexToAddress(uint256 index) internal pure returns (address) {
        return address(uint160(uint256(keccak256(abi.encodePacked("addr", index)))));
    }

    /**
     * @notice Convert address to hex string
     */
    function _addressToString(address addr) internal pure returns (string memory) {
        bytes memory result = new bytes(42);
        result[0] = "0";
        result[1] = "x";

        uint160 value = uint160(addr);
        for (uint i = 0; i < 20; i++) {
            uint8 byteValue = uint8(value >> (8 * (19 - i)));
            result[2 + i * 2] = _hexChar(byteValue >> 4);
            result[2 + i * 2 + 1] = _hexChar(byteValue & 0x0f);
        }

        return string(result);
    }

    /**
     * @notice Convert 4-bit value to hex character
     */
    function _hexChar(uint8 value) internal pure returns (bytes1) {
        if (value < 10) {
            return bytes1(uint8(bytes1("0")) + value);
        } else {
            return bytes1(uint8(bytes1("a")) + value - 10);
        }
    }

    /**
     * @notice Parse hex address string to uint256
     */
    function _parseHexAddress(string memory hexStr) internal pure returns (uint256) {
        bytes memory b = bytes(hexStr);
        uint256 result = 0;
        uint256 start = 0;

        // Skip 0x prefix if present
        if (b.length >= 2 && b[0] == "0" && b[1] == "x") {
            start = 2;
        }

        for (uint i = start; i < b.length; i++) {
            result = result * 16;
            if (b[i] >= "0" && b[i] <= "9") {
                result += uint8(b[i]) - uint8(bytes1("0"));
            } else if (b[i] >= "a" && b[i] <= "f") {
                result += uint8(b[i]) - uint8(bytes1("a")) + 10;
            } else if (b[i] >= "A" && b[i] <= "F") {
                result += uint8(b[i]) - uint8(bytes1("A")) + 10;
            }
        }

        return result;
    }
}
