// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "forge-std/Test.sol";

abstract contract YulTestBase is Test {
    function _coerceRandomUint256(uint256 prng, uint256 smallMod) internal pure returns (uint256) {
        uint256 selector = prng % 16;
        if (selector == 0) return 0;
        if (selector == 1) return 1;
        if (selector == 2) return type(uint256).max;
        if (selector == 3) return type(uint256).max - 1;
        if (selector == 4) return 2 ** 128;
        if (selector == 5) return 2 ** 255;
        if (smallMod == 0) return prng;
        return prng % smallMod;
    }

    function _compileYul(string memory path) internal returns (bytes memory) {
        string[] memory cmds = new string[](3);
        cmds[0] = "bash";
        cmds[1] = "-lc";
        cmds[2] = string.concat(
            "solc --strict-assembly --bin ",
            path,
            " | grep -E '^[0-9a-fA-F]+$' | tail -n 1"
        );
        bytes memory out = vm.ffi(cmds);
        bytes memory trimmed = _trimBytes(out);
        if (_isHexBytes(trimmed)) {
            return vm.parseBytes(string.concat("0x", string(trimmed)));
        }
        return trimmed;
    }

    function _deploy(bytes memory bytecode) internal returns (address addr) {
        assembly {
            addr := create(0, add(bytecode, 0x20), mload(bytecode))
        }
        require(addr != address(0), "Yul deploy failed");
    }

    function deployYul(string memory name) internal returns (address) {
        string memory path = string.concat("compiler/yul/", name, ".yul");
        return _deploy(_compileYul(path));
    }

    function deployYulWithArgs(string memory name, bytes memory args) internal returns (address) {
        string memory path = string.concat("compiler/yul/", name, ".yul");
        bytes memory initCode = bytes.concat(_compileYul(path), args);
        return _deploy(initCode);
    }

    function _trimBytes(bytes memory input) internal pure returns (bytes memory) {
        uint256 start = 0;
        uint256 end = input.length;
        while (start < end && _isWhitespace(input[start])) {
            start++;
        }
        while (end > start && _isWhitespace(input[end - 1])) {
            end--;
        }
        bytes memory out = new bytes(end - start);
        for (uint256 i = 0; i < out.length; i++) {
            out[i] = input[start + i];
        }
        return out;
    }

    function _isHexBytes(bytes memory input) internal pure returns (bool) {
        if (input.length == 0) {
            return false;
        }
        for (uint256 i = 0; i < input.length; i++) {
            if (!_isHexChar(input[i])) {
                return false;
            }
        }
        return true;
    }

    function _isHexChar(bytes1 c) private pure returns (bool) {
        return (c >= 0x30 && c <= 0x39) || (c >= 0x41 && c <= 0x46) || (c >= 0x61 && c <= 0x66);
    }

    function _isWhitespace(bytes1 c) private pure returns (bool) {
        return c == 0x20 || c == 0x0a || c == 0x0d || c == 0x09;
    }
}
