// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "./GeneratedBase.t.sol";

contract GeneratedCompareAndSwapTest is GeneratedBase {
    function testCompareAndSwap() public {
        bytes memory creation = _readHexFile("out/example.creation.bin");
        address deployed = _deploy(creation);

        bytes4 selGet = 0x7eba7ba6;
        bytes4 selSet = 0xf2c298be;
        bytes4 selCas = 0xc74962fa;

        (bool ok,) = deployed.call(abi.encodeWithSelector(selSet, 10, 41));
        require(ok, "setSlot failed");

        (ok,) = deployed.call(abi.encodeWithSelector(selCas, 10, 41, 99));
        require(ok, "compareAndSwap should succeed");

        bytes memory data;
        (ok, data) = deployed.call(abi.encodeWithSelector(selGet, 10));
        require(ok, "getSlot failed");
        uint256 val = abi.decode(data, (uint256));
        require(val == 99, "unexpected compareAndSwap value");

        (ok,) = deployed.call(abi.encodeWithSelector(selCas, 10, 1, 123));
        require(!ok, "compareAndSwap should revert on mismatch");
    }
}
