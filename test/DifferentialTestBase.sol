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
     * @dev Expects format: {"returnValue":123,...}
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

        // Skip whitespace
        while (start < b.length && (b[start] == ' ' || b[start] == '\t' || b[start] == '\n')) {
            start++;
        }

        // Parse number
        return _extractNumber(json, start);
    }

    /**
     * @notice Extract storage change from EDSL JSON response
     * @dev Expects format: {"storageChanges":[[slot,value],...]}
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
     * @notice Linear congruential generator for pseudo-random numbers
     * @dev Used for deterministic random test generation
     */
    function _prng(uint256 seed) internal pure returns (uint256) {
        // LCG parameters (same as used in DiffTestConfig)
        uint256 a = 1664525;
        uint256 c = 1013904223;
        uint256 m = 2 ** 31;
        return (a * seed + c) % m;
    }

    /**
     * @notice Skip forward N iterations of PRNG
     */
    function _skipRandom(uint256 seed, uint256 iterations) internal pure returns (uint256) {
        uint256 current = seed;
        for (uint i = 0; i < iterations; i++) {
            current = _prng(current);
        }
        return current;
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
