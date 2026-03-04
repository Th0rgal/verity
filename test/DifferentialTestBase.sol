// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

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
     * @dev Expects format: {"returnValue":"123",...} or {"returnValue":"0x..."}
     *      The value is quoted in the JSON output. Handles both decimal and hex.
     */
    function _extractReturnValue(string memory json) internal pure returns (uint256) {
        bytes memory jsonBytes = bytes(json);
        bytes memory searchBytes = bytes("\"returnValue\":\"");

        if (jsonBytes.length < searchBytes.length) return 0;

        for (uint i = 0; i <= jsonBytes.length - searchBytes.length; i++) {
            bool found = true;
            for (uint j = 0; j < searchBytes.length; j++) {
                if (jsonBytes[i + j] != searchBytes[j]) {
                    found = false;
                    break;
                }
            }
            if (found) {
                uint start = i + searchBytes.length;
                uint end = start;
                while (end < jsonBytes.length && jsonBytes[end] != bytes1('"')) {
                    end++;
                }
                bytes memory numBytes = new bytes(end - start);
                for (uint k = 0; k < end - start; k++) {
                    numBytes[k] = jsonBytes[start + k];
                }
                // Handle hex addresses (0x prefix)
                if (numBytes.length >= 2 && numBytes[0] == '0' &&
                    (numBytes[1] == 'x' || numBytes[1] == 'X')) {
                    return _parseHexAddress(string(numBytes));
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
     * @notice Extract address storage change from EDSL JSON storageAddrChanges
     * @dev Expects format: {"storageAddrChanges":[{"slot":X,"value":"0x..."},...]}
     */
    function _extractStorageAddrChange(string memory json, uint256 slot)
        internal
        pure
        returns (bool, uint256)
    {
        if (!contains(json, "\"storageAddrChanges\"")) {
            return (false, 0);
        }

        bytes memory jsonBytes = bytes(json);
        bytes memory slotPattern = bytes(string.concat("\"slot\":", _uintToString(slot)));

        if (jsonBytes.length < slotPattern.length) return (false, 0);
        for (uint i = 0; i <= jsonBytes.length - slotPattern.length; i++) {
            bool foundSlot = true;
            for (uint j = 0; j < slotPattern.length; j++) {
                if (jsonBytes[i + j] != slotPattern[j]) {
                    foundSlot = false;
                    break;
                }
            }
            if (foundSlot) {
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
                        uint start = k + valuePattern.length;
                        // Skip optional quote
                        if (start < jsonBytes.length && jsonBytes[start] == '"') {
                            start++;
                        }
                        uint end = start;
                        while (end < jsonBytes.length &&
                               jsonBytes[end] != '"' &&
                               jsonBytes[end] != ',' &&
                               jsonBytes[end] != '}') {
                            end++;
                        }
                        bytes memory valueBytes = new bytes(end - start);
                        for (uint m = 0; m < end - start; m++) {
                            valueBytes[m] = jsonBytes[start + m];
                        }
                        string memory valueStr = string(valueBytes);
                        if (valueBytes.length >= 2 && valueBytes[0] == '0' &&
                            (valueBytes[1] == 'x' || valueBytes[1] == 'X')) {
                            return (true, _parseHexAddress(valueStr));
                        }
                        return (true, _stringToUint(valueStr));
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
    function _extractNumber(string memory json, uint256 startIdx) internal pure virtual returns (uint256) {
        bytes memory jsonBytes = bytes(json);
        uint256 result = 0;
        bool foundDigit = false;

        for (uint i = startIdx; i < jsonBytes.length; i++) {
            bytes1 c = jsonBytes[i];
            if (c >= '0' && c <= '9') {
                unchecked { result = result * 10 + uint8(c) - uint8(bytes1('0')); }
                foundDigit = true;
            } else if (foundDigit) {
                break;
            }
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
    function _indexToAddress(uint256 index) internal pure virtual returns (address) {
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
     * @notice Shell preamble for invoking the difftest interpreter
     */
    function _interpreterPreamble() internal pure returns (string memory) {
        return string.concat(
            "cd \"$(git rev-parse --show-toplevel)\" && export PATH=\"$HOME/.elan/bin:$PATH\" && ",
            "if [ ! -x ./.lake/build/bin/difftest-interpreter ]; then ",
            "mkdir -p .lake/build/bin && lake build difftest-interpreter >/dev/null; ",
            "fi; ",
            "./.lake/build/bin/difftest-interpreter"
        );
    }

    /**
     * @notice Extract a mapping value for a given address key from EDSL JSON
     * @param keyStr The address as a hex string (e.g. "0xABCD...")
     */
    function _extractMappingValue(string memory json, string memory keyStr) internal pure returns (uint256) {
        bytes memory jsonBytes = bytes(json);
        bytes memory keyBytes = bytes(keyStr);
        bytes memory keyBytesLower = bytes(_toLowerCase(keyStr));

        if (jsonBytes.length < keyBytes.length) return 0;

        for (uint i = 0; i <= jsonBytes.length - keyBytes.length; i++) {
            bool found = true;
            bool foundLower = true;
            for (uint j = 0; j < keyBytes.length; j++) {
                if (jsonBytes[i + j] != keyBytes[j]) {
                    found = false;
                }
                if (jsonBytes[i + j] != keyBytesLower[j]) {
                    foundLower = false;
                }
                if (!found && !foundLower) break;
            }
            if (found || foundLower) {
                if (jsonBytes.length < 8) return 0;
                for (uint k = i + keyBytes.length; k < jsonBytes.length - 7; k++) {
                    if (jsonBytes[k] == '"' && jsonBytes[k+1] == 'v' &&
                        jsonBytes[k+2] == 'a' && jsonBytes[k+3] == 'l' &&
                        jsonBytes[k+4] == 'u' && jsonBytes[k+5] == 'e' &&
                        jsonBytes[k+6] == '"' && jsonBytes[k+7] == ':') {
                        return _extractNumber(json, k + 8);
                    }
                }
            }
        }
        return 0;
    }

    /**
     * @notice Extract mapping change from EDSL JSON by (slot, address-key)
     * @dev Expects objects encoded as {"slot":S,"key":"0x..","value":V}
     */
    function _extractMappingChange(string memory json, uint256 slot, address key)
        internal
        pure
        returns (bool found, uint256 value)
    {
        string memory keyStr = _toLowerCase(_addressToString(key));
        bytes memory pattern = bytes(
            string.concat(
                "\"slot\":",
                _uintToString(slot),
                ",\"key\":\"",
                keyStr,
                "\",\"value\":"
            )
        );
        bytes memory jsonBytes = bytes(json);
        if (jsonBytes.length < pattern.length) return (false, 0);

        for (uint256 i = 0; i <= jsonBytes.length - pattern.length; i++) {
            bool matches = true;
            for (uint256 j = 0; j < pattern.length; j++) {
                if (jsonBytes[i + j] != pattern[j]) {
                    matches = false;
                    break;
                }
            }
            if (matches) {
                return (true, _extractNumber(json, i + pattern.length));
            }
        }
        return (false, 0);
    }

    /**
     * @notice Extract mappingUint change from EDSL JSON by (slot, uint-key)
     * @dev Expects objects encoded as {"slot":S,"key":K,"value":V}
     */
    function _extractMappingUintChange(string memory json, uint256 slot, uint256 key)
        internal
        pure
        returns (bool found, uint256 value)
    {
        bytes memory pattern = bytes(
            string.concat(
                "\"slot\":",
                _uintToString(slot),
                ",\"key\":",
                _uintToString(key),
                ",\"value\":"
            )
        );
        bytes memory jsonBytes = bytes(json);
        if (jsonBytes.length < pattern.length) return (false, 0);

        for (uint256 i = 0; i <= jsonBytes.length - pattern.length; i++) {
            bool matches = true;
            for (uint256 j = 0; j < pattern.length; j++) {
                if (jsonBytes[i + j] != pattern[j]) {
                    matches = false;
                    break;
                }
            }
            if (matches) {
                return (true, _extractNumber(json, i + pattern.length));
            }
        }
        return (false, 0);
    }

    /**
     * @notice Extract mapping2 change from EDSL JSON by (slot, key1, key2)
     * @dev Expects objects encoded as {"slot":S,"key1":"0x..","key2":"0x..","value":V}
     */
    function _extractMapping2Change(string memory json, uint256 slot, address key1, address key2)
        internal
        pure
        returns (bool found, uint256 value)
    {
        string memory key1Str = _toLowerCase(_addressToString(key1));
        string memory key2Str = _toLowerCase(_addressToString(key2));
        bytes memory pattern = bytes(
            string.concat(
                "\"slot\":",
                _uintToString(slot),
                ",\"key1\":\"",
                key1Str,
                "\",\"key2\":\"",
                key2Str,
                "\",\"value\":"
            )
        );
        bytes memory jsonBytes = bytes(json);
        if (jsonBytes.length < pattern.length) return (false, 0);

        for (uint256 i = 0; i <= jsonBytes.length - pattern.length; i++) {
            bool matches = true;
            for (uint256 j = 0; j < pattern.length; j++) {
                if (jsonBytes[i + j] != pattern[j]) {
                    matches = false;
                    break;
                }
            }
            if (matches) {
                return (true, _extractNumber(json, i + pattern.length));
            }
        }
        return (false, 0);
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
