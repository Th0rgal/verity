// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";

contract SelectorSanityTest is Test {
    function testYulSelectorsMatchAbi() public {
        _assertSelector("compiler/yul/Counter.yul", "increment()");
        _assertSelector("compiler/yul/Counter.yul", "decrement()");
        _assertSelector("compiler/yul/Counter.yul", "getCount()");

        _assertSelector("compiler/yul/SafeCounter.yul", "increment()");
        _assertSelector("compiler/yul/SafeCounter.yul", "decrement()");
        _assertSelector("compiler/yul/SafeCounter.yul", "getCount()");

        _assertSelector("compiler/yul/SimpleStorage.yul", "store(uint256)");
        _assertSelector("compiler/yul/SimpleStorage.yul", "retrieve()");

        _assertSelector("compiler/yul/Owned.yul", "transferOwnership(address)");
        _assertSelector("compiler/yul/Owned.yul", "getOwner()");

        _assertSelector("compiler/yul/OwnedCounter.yul", "increment()");
        _assertSelector("compiler/yul/OwnedCounter.yul", "decrement()");
        _assertSelector("compiler/yul/OwnedCounter.yul", "getCount()");
        _assertSelector("compiler/yul/OwnedCounter.yul", "getOwner()");
        _assertSelector("compiler/yul/OwnedCounter.yul", "transferOwnership(address)");

        _assertSelector("compiler/yul/Ledger.yul", "deposit(uint256)");
        _assertSelector("compiler/yul/Ledger.yul", "withdraw(uint256)");
        _assertSelector("compiler/yul/Ledger.yul", "transfer(address,uint256)");
        _assertSelector("compiler/yul/Ledger.yul", "getBalance(address)");

        _assertSelector("compiler/yul/SimpleToken.yul", "mint(address,uint256)");
        _assertSelector("compiler/yul/SimpleToken.yul", "transfer(address,uint256)");
        _assertSelector("compiler/yul/SimpleToken.yul", "balanceOf(address)");
        _assertSelector("compiler/yul/SimpleToken.yul", "totalSupply()");
        _assertSelector("compiler/yul/SimpleToken.yul", "owner()");
    }

    function _assertSelector(string memory path, string memory signature) internal {
        string memory yul = vm.readFile(path);
        bytes4 selector = bytes4(keccak256(bytes(signature)));
        string memory needle = string.concat("case 0x", _bytes4ToHex(selector));
        assertTrue(
            _contains(yul, needle),
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
}
