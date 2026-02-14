// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import {console2} from "forge-std/Test.sol";

/**
 * @title DifferentialTestBase
 * @notice Shared utilities for differential testing across all contracts
 *
 * Provides common JSON parsing, string manipulation, and test helper functions
 * used by all differential test suites. This eliminates ~800 lines of duplicated
 * code across the 7 differential test files.
 *
 * @dev This contract is abstract and must be inherited by concrete test contracts.
 *      It does not modify any state - all functions are pure or view.
 */
abstract contract DifferentialTestBase {
    /// @notice Test result counters (subclasses can use these)
    uint256 public testsPassed;
    uint256 public testsFailed;

    /*//////////////////////////////////////////////////////////////
                           JSON PARSING UTILITIES
    //////////////////////////////////////////////////////////////*/

    /**
     * @notice Extract returnValue from EDSL JSON response
     * @dev Expects format: {"returnValue":"123",...} or {"returnValue":123,...}
     * @param json The JSON string to parse
     * @return The extracted uint256 value
     */
    function _extractReturnValue(string memory json) internal pure returns (uint256) {
        bytes memory b = bytes(json);
        uint256 start = 0;
        bool foundKey = false;

        // Find "returnValue":
        for (uint i = 0; i + 13 < b.length; i++) {
            if (
                b[i] == '"' && b[i + 1] == 'r' && b[i + 2] == 'e' && b[i + 3] == 't'
                    && b[i + 4] == 'u' && b[i + 5] == 'r' && b[i + 6] == 'n' && b[i + 7] == 'V'
                    && b[i + 8] == 'a' && b[i + 9] == 'l' && b[i + 10] == 'u' && b[i + 11] == 'e'
                    && b[i + 12] == '"' && b[i + 13] == ':'
            ) {
                start = i + 14;
                foundKey = true;
                break;
            }
        }

        require(foundKey, "returnValue not found in JSON");

        // Skip whitespace and optional quote
        while (start < b.length && (b[start] == ' ' || b[start] == '\t' || b[start] == '\n' || b[start] == '"')) {
            start++;
        }

        // Parse number
        return _extractNumber(json, start);
    }

    /**
     * @notice Extract storage change from EDSL JSON response
     * @dev Expects format: {"storageChanges":[[slot,value],...]}
     * @param json The JSON string to parse
     * @param slot The storage slot to find
     * @return found Whether the slot was found
     * @return value The value at the slot (0 if not found)
     */
    function _extractStorageChange(string memory json, uint256 slot)
        internal
        pure
        returns (bool found, uint256 value)
    {
        bytes memory b = bytes(json);

        // Find "storageChanges":
        uint256 arrayStart = 0;
        for (uint i = 0; i + 17 < b.length; i++) {
            if (
                b[i] == '"' && b[i + 1] == 's' && b[i + 2] == 't' && b[i + 3] == 'o'
                    && b[i + 4] == 'r' && b[i + 5] == 'a' && b[i + 6] == 'g' && b[i + 7] == 'e'
                    && b[i + 8] == 'C' && b[i + 9] == 'h' && b[i + 10] == 'a' && b[i + 11] == 'n'
                    && b[i + 12] == 'g' && b[i + 13] == 'e' && b[i + 14] == 's' && b[i + 15] == '"'
                    && b[i + 16] == ':'
            ) {
                arrayStart = i + 17;
                break;
            }
        }

        if (arrayStart == 0) return (false, 0);

        // Find opening [
        while (arrayStart < b.length && b[arrayStart] != "[") {
            arrayStart++;
        }
        arrayStart++;

        // Parse array of [slot, value] pairs
        uint256 pos = arrayStart;
        while (pos < b.length && b[pos] != "]") {
            // Skip whitespace
            while (pos < b.length && (b[pos] == " " || b[pos] == "\t" || b[pos] == "\n")) {
                pos++;
            }

            if (b[pos] == "[") {
                pos++;
                // Parse slot number
                uint256 foundSlot = _extractNumber(json, pos);

                // Skip to comma
                while (pos < b.length && b[pos] != ",") {
                    pos++;
                }
                pos++;

                // Parse value
                uint256 foundValue = _extractNumber(json, pos);

                if (foundSlot == slot) {
                    return (true, foundValue);
                }

                // Skip to end of pair ]
                while (pos < b.length && b[pos] != "]") {
                    pos++;
                }
                pos++;
            }

            // Skip comma
            if (pos < b.length && b[pos] == ",") {
                pos++;
            }
        }

        return (false, 0);
    }

    /**
     * @notice Parse a number from JSON starting at given index
     * @dev Handles both quoted and unquoted numbers
     * @param json The JSON string
     * @param startIdx Starting index
     * @return The parsed uint256 value
     */
    function _extractNumber(string memory json, uint256 startIdx) internal pure returns (uint256) {
        bytes memory b = bytes(json);
        uint256 result = 0;
        uint256 i = startIdx;

        // Skip whitespace and optional opening quote
        while (i < b.length && (b[i] == " " || b[i] == "\t" || b[i] == "\n" || b[i] == '"')) {
            i++;
        }

        // Parse digits
        while (i < b.length && b[i] >= "0" && b[i] <= "9") {
            result = result * 10 + uint8(b[i]) - uint8(bytes1("0"));
            i++;
        }

        return result;
    }

    /*//////////////////////////////////////////////////////////////
                          STRING UTILITIES
    //////////////////////////////////////////////////////////////*/

    /**
     * @notice Check if a string contains a substring
     * @param str The string to search in
     * @param substr The substring to find
     * @return true if substr is found in str
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
     * @notice Convert string to uint256
     * @param s The string to convert (must contain only digits)
     * @return The parsed uint256 value
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
     * @param str The string to convert
     * @return The lowercase version
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
     * @notice Convert address to hex string (0x prefixed, lowercase)
     * @param addr The address to convert
     * @return The hex string representation
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
     * @notice Convert 4-bit value to lowercase hex character
     * @param value The value (0-15)
     * @return The hex character ('0'-'9' or 'a'-'f')
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
     * @dev Handles both 0x-prefixed and non-prefixed strings
     * @param hexStr The hex string to parse
     * @return The parsed uint256 value
     */
    function _parseHexAddress(string memory hexStr) internal pure returns (uint256) {
        bytes memory b = bytes(hexStr);
        uint256 result = 0;
        uint256 start = 0;

        // Skip 0x prefix if present
        if (b.length >= 2 && b[0] == "0" && (b[1] == "x" || b[1] == "X")) {
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

    /*//////////////////////////////////////////////////////////////
                           TEST HELPERS
    //////////////////////////////////////////////////////////////*/

    /**
     * @notice Linear congruential generator for pseudo-random numbers
     * @dev Uses parameters: a=1664525, c=1013904223, m=2^31
     *      Same as used in DiffTestConfig for consistency
     * @param seed The current seed value
     * @return The next pseudo-random value
     */
    function _prng(uint256 seed) internal pure returns (uint256) {
        uint256 a = 1664525;
        uint256 c = 1013904223;
        uint256 m = 2 ** 31;
        return (a * seed + c) % m;
    }

    /**
     * @notice Skip forward N iterations of PRNG
     * @param seed The starting seed
     * @param iterations Number of iterations to skip
     * @return The seed after N iterations
     */
    function _skipRandom(uint256 seed, uint256 iterations) internal pure returns (uint256) {
        uint256 current = seed;
        for (uint i = 0; i < iterations; i++) {
            current = _prng(current);
        }
        return current;
    }

    /**
     * @notice Convert index to deterministic address using keccak256
     * @dev Generates consistent addresses for testing
     * @param index The index value
     * @return A deterministic address
     */
    function _indexToAddress(uint256 index) internal pure returns (address) {
        return address(uint160(uint256(keccak256(abi.encodePacked("addr", index)))));
    }
}
