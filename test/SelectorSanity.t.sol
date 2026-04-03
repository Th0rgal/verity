// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

contract SelectorSanityTest is YulTestBase {
    function testYulSelectorsMatchAbi() public {
        _ensureVerityManifestYul("packages/verity-examples/contracts.manifest", "Vault", _yulDir());

        _assertSelector(_yulPath("Counter"), "increment()");
        _assertSelector(_yulPath("Counter"), "decrement()");
        _assertSelector(_yulPath("Counter"), "getCount()");

        _assertSelector(_yulPath("SafeCounter"), "increment()");
        _assertSelector(_yulPath("SafeCounter"), "decrement()");
        _assertSelector(_yulPath("SafeCounter"), "getCount()");

        _assertSelector(_yulPath("SimpleStorage"), "store(uint256)");
        _assertSelector(_yulPath("SimpleStorage"), "retrieve()");

        _assertSelector(_yulPath("Owned"), "transferOwnership(address)");
        _assertSelector(_yulPath("Owned"), "getOwner()");

        _assertSelector(_yulPath("OwnedCounter"), "increment()");
        _assertSelector(_yulPath("OwnedCounter"), "decrement()");
        _assertSelector(_yulPath("OwnedCounter"), "getCount()");
        _assertSelector(_yulPath("OwnedCounter"), "getOwner()");
        _assertSelector(_yulPath("OwnedCounter"), "transferOwnership(address)");

        _assertSelector(_yulPath("Ledger"), "deposit(uint256)");
        _assertSelector(_yulPath("Ledger"), "withdraw(uint256)");
        _assertSelector(_yulPath("Ledger"), "transfer(address,uint256)");
        _assertSelector(_yulPath("Ledger"), "getBalance(address)");

        _assertSelector(_yulPath("Vault"), "deposit(uint256)");
        _assertSelector(_yulPath("Vault"), "withdraw(uint256)");
        _assertSelector(_yulPath("Vault"), "balanceOf(address)");
        _assertSelector(_yulPath("Vault"), "totalAssets()");
        _assertSelector(_yulPath("Vault"), "totalSupply()");

        _assertSelector(_yulPath("SimpleToken"), "mint(address,uint256)");
        _assertSelector(_yulPath("SimpleToken"), "transfer(address,uint256)");
        _assertSelector(_yulPath("SimpleToken"), "balanceOf(address)");
        _assertSelector(_yulPath("SimpleToken"), "totalSupply()");
        _assertSelector(_yulPath("SimpleToken"), "owner()");
    }

    function _yulPath(string memory contractName) internal view returns (string memory) {
        return string.concat(_yulDir(), "/", contractName, ".yul");
    }

    function _assertSelector(string memory path, string memory signature) internal view {
        string memory yul = vm.readFile(path);
        bytes4 selector = bytes4(keccak256(bytes(signature)));
        string memory selectorHex = _bytes4ToHex(selector);
        string memory needle = string.concat("case 0x", selectorHex);
        string memory compactNeedle = string.concat("case 0x", _trimLeadingZeroHex(selectorHex));
        assertTrue(
            _contains(yul, needle) || _contains(yul, compactNeedle),
            string.concat("Missing selector for ", signature, " in ", path)
        );
    }

    function _bytes4ToHex(bytes4 data) internal pure returns (string memory) {
        bytes memory hexChars = "0123456789abcdef";
        bytes memory out = new bytes(8);
        for (uint256 i = 0; i < 4; i++) {
            uint8 b = uint8(data[i]);
            out[i * 2] = hexChars[b >> 4];
            out[i * 2 + 1] = hexChars[b & 0x0f];
        }
        return string(out);
    }

    function _contains(string memory haystack, string memory needle) internal pure returns (bool) {
        bytes memory h = bytes(haystack);
        bytes memory n = bytes(needle);
        if (n.length == 0) {
            return true;
        }
        if (h.length < n.length) {
            return false;
        }
        for (uint256 i = 0; i <= h.length - n.length; i++) {
            bool matchFound = true;
            for (uint256 j = 0; j < n.length; j++) {
                if (h[i + j] != n[j]) {
                    matchFound = false;
                    break;
                }
            }
            if (matchFound) {
                return true;
            }
        }
        return false;
    }

    function _trimLeadingZeroHex(string memory hexValue) internal pure returns (string memory) {
        bytes memory raw = bytes(hexValue);
        uint256 start = 0;
        while (start + 1 < raw.length && raw[start] == "0") {
            start++;
        }
        bytes memory out = new bytes(raw.length - start);
        for (uint256 i = 0; i < out.length; i++) {
            out[i] = raw[start + i];
        }
        return string(out);
    }
}
