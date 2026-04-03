// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "forge-std/Test.sol";

abstract contract YulTestBase is Test {
    function _usePatchedVerityCompiler() internal view returns (bool) {
        return keccak256(bytes(_yulDir())) == keccak256(bytes("compiler/yul-patched"));
    }

    function _verityCompilerBinName() internal view returns (string memory) {
        if (_usePatchedVerityCompiler()) {
            return "verity-compiler-patched";
        }
        return "verity-compiler";
    }

    function _verityCompilerBuildTarget() internal view returns (string memory) {
        if (_usePatchedVerityCompiler()) {
            return "verity-compiler-patched";
        }
        return "verity-compiler";
    }

    function _verityCompilerArgs() internal view returns (string memory) {
        if (_usePatchedVerityCompiler()) {
            return " --enable-patches";
        }
        return "";
    }

    function _yulDir() internal view returns (string memory) {
        string memory envDir = vm.envOr("DIFFTEST_YUL_DIR", string(""));
        if (bytes(envDir).length != 0) {
            return envDir;
        }
        if (vm.exists("compiler/yul")) {
            return "compiler/yul";
        }
        return "artifacts/yul";
    }

    // Edge-case values matching Lean's edgeUint256Values and DiffTestConfig._edgeUintValues():
    //   [0, 1, 2, 2^128, 2^255, 2^256-2, 2^256-1]
    // Selectors 0-6 return these edge values (~7/16 probability);
    // selectors 7-15 return prng % smallMod (~9/16 probability).
    function _coerceRandomUint256(uint256 prng, uint256 smallMod) internal pure returns (uint256) {
        uint256 selector = prng % 16;
        if (selector == 0) return 0;
        if (selector == 1) return 1;
        if (selector == 2) return 2;
        if (selector == 3) return 2 ** 128;
        if (selector == 4) return 2 ** 255;
        if (selector == 5) return type(uint256).max - 1;
        if (selector == 6) return type(uint256).max;
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
        string memory path = string.concat(_yulDir(), "/", name, ".yul");
        return _deploy(_compileYul(path));
    }

    function _ensureVerityModuleYul(
        string memory moduleName,
        string memory contractName,
        string memory outDir
    ) internal {
        string memory artifactPath = string.concat(outDir, "/", contractName, ".yul");
        string[] memory cmds = new string[](3);
        cmds[0] = "bash";
        cmds[1] = "-lc";
        cmds[2] = string.concat(
            "artifact='",
            artifactPath,
            "'; out='",
            outDir,
            "'; module='",
            moduleName,
            "'; compiler_name='",
            _verityCompilerBinName(),
            "'; compiler_target='",
            _verityCompilerBuildTarget(),
            "'; compiler_args='",
            _verityCompilerArgs(),
            "'; ",
            "compiler=\"./.lake/build/bin/$compiler_name\"; ",
            "if [ ! -x \"$compiler\" ] && [ -x \"./compiler/bin/$compiler_name\" ]; then compiler=\"./compiler/bin/$compiler_name\"; fi; ",
            "if [ -f \"$artifact\" ] && [ -x \"$compiler\" ] && [ \"$compiler\" -ot \"$artifact\" ] && ",
            "! find Contracts Compiler Verity -name '*.lean' -newer \"$artifact\" -print -quit | grep -q .; then exit 0; fi; ",
            "mkdir -p \"$out\" && lake build \"$module\" \"$compiler_target\" >/dev/null && ",
            "\"$compiler\" --module \"$module\" --output \"$out\" $compiler_args >/dev/null"
        );
        vm.ffi(cmds);
        require(vm.exists(artifactPath), "Verity module compile did not emit Yul artifact");
    }

    function _ensureVerityManifestYul(
        string memory manifestPath,
        string memory contractName,
        string memory outDir
    ) internal {
        string memory artifactPath = string.concat(outDir, "/", contractName, ".yul");
        string[] memory cmds = new string[](3);
        cmds[0] = "bash";
        cmds[1] = "-lc";
        cmds[2] = string.concat(
            "artifact='",
            artifactPath,
            "'; out='",
            outDir,
            "'; manifest='",
            manifestPath,
            "'; compiler_name='",
            _verityCompilerBinName(),
            "'; compiler_target='",
            _verityCompilerBuildTarget(),
            "'; compiler_args='",
            _verityCompilerArgs(),
            "'; ",
            "compiler=\"./.lake/build/bin/$compiler_name\"; ",
            "if [ ! -x \"$compiler\" ] && [ -x \"./compiler/bin/$compiler_name\" ]; then compiler=\"./compiler/bin/$compiler_name\"; fi; ",
            "if [ -f \"$artifact\" ] && [ -x \"$compiler\" ] && [ \"$compiler\" -ot \"$artifact\" ] && [ \"$manifest\" -ot \"$artifact\" ] && ",
            "! find Contracts Compiler Verity -name '*.lean' -newer \"$artifact\" -print -quit | grep -q .; then exit 0; fi; ",
            "mkdir -p \"$out\" && set -- $(grep -vE '^[[:space:]]*($|#)' \"$manifest\") && lake build \"$@\" \"$compiler_target\" >/dev/null && ",
            "\"$compiler\" --manifest \"$manifest\" --output \"$out\" $compiler_args >/dev/null"
        );
        vm.ffi(cmds);
        require(vm.exists(artifactPath), "Verity manifest compile did not emit Yul artifact");
    }

    function deployCompiledVerityModule(
        string memory moduleName,
        string memory contractName,
        string memory outDir
    ) internal returns (address) {
        _ensureVerityModuleYul(moduleName, contractName, outDir);
        string memory path = string.concat(outDir, "/", contractName, ".yul");
        return _deploy(_compileYul(path));
    }

    function deployYulWithArgs(string memory name, bytes memory args) internal returns (address) {
        string memory path = string.concat(_yulDir(), "/", name, ".yul");
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

    function readStorage(address target, uint256 slot) internal view returns (uint256) {
        return uint256(vm.load(target, bytes32(slot)));
    }

    function readStorageAddr(address target, uint256 slot) internal view returns (address) {
        return address(uint160(uint256(vm.load(target, bytes32(slot)))));
    }

    function _mappingSlot(bytes32 key, uint256 baseSlot) internal pure returns (bytes32) {
        return keccak256(abi.encode(key, baseSlot));
    }

    function _nestedMappingSlot(bytes32 key0, bytes32 key1, uint256 baseSlot) internal pure returns (bytes32) {
        bytes32 outer = _mappingSlot(key0, baseSlot);
        return keccak256(abi.encode(key1, outer));
    }

    function _mappingWordSlot(bytes32 key, uint256 baseSlot, uint256 wordOffset) internal pure returns (bytes32) {
        return bytes32(uint256(_mappingSlot(key, baseSlot)) + wordOffset);
    }
}
